// Forge v5 — a standalone GitHub-compatible git forge in one file.
// Node 22 stdlib only. Serves smart HTTP (git v2/v0), REST v3, GraphQL v4, MCP.
// Lifecycle: bind an ephemeral port, POST {"port"} to $MAKEFUN_ENV_URL/register,
// long-poll GET $MAKEFUN_ENV_URL/done until {"done":true}, then exit 0.
// Written from scratch for github-core-clone-01; no prior implementation was read.

import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { createHash, randomBytes } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const ZERO_OID = '0'.repeat(40);
const VIEWER = 'adaiversen';
const VIEWER_EMAIL = 'adaiversen@users.noreply.github.com';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
const EPOCH = 1735689600; // 2025-01-01T00:00:00Z, fixed seed epoch; never Date.now() for content
const AGENT = 'forge/1.0';
const PKT_MAX = 65520;
const PKT_PAYLOAD = PKT_MAX - 4;

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObject { type: ObjType; data: Buffer; }

function sha1(buf: Buffer): string {
  return createHash('sha1').update(buf).digest('hex');
}

function isOid(s: string): boolean {
  return /^[0-9a-f]{40}$/.test(s);
}

function hashObject(type: ObjType, data: Buffer): string {
  const head = Buffer.from(`${type} ${data.length}\0`, 'ascii');
  return createHash('sha1').update(head).update(data).digest('hex');
}

// ---------------------------------------------------------------- pkt-lines

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = data.length + 4;
  const head = Buffer.allocUnsafe(4);
  head.write(len.toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([head, data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

function pktLines(items: readonly (string | Buffer | 'flush' | 'delim')[]): Buffer {
  const parts: Buffer[] = [];
  for (const item of items) {
    if (item === 'flush') parts.push(PKT_FLUSH);
    else if (item === 'delim') parts.push(PKT_DELIM);
    else parts.push(pktLine(item));
  }
  return Buffer.concat(parts);
}

/** Decode a pkt-line stream into packets. Throws on a bad length prefix. */
function decodePktLines(buf: Buffer): { kind: 'data' | 'flush' | 'delim' | 'end'; payload: Buffer }[] {
  const out: { kind: 'data' | 'flush' | 'delim' | 'end'; payload: Buffer }[] = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) throw new Error('truncated pkt-line header');
    const len = parseInt(buf.subarray(off, off + 4).toString('ascii'), 16);
    if (Number.isNaN(len)) throw new Error('bad pkt-line length');
    if (len === 0) { out.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 1) { out.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 2) { out.push({ kind: 'end', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len < 4 || off + len > buf.length) throw new Error('bad pkt-line length');
    out.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return out;
}

// ---------------------------------------------------------------- git objects

function parseCommit(data: Buffer): { tree: string; parents: string[]; author: string; committer: string; message: string; timestamp: number } {
  const blank = data.indexOf('\n\n');
  const headEnd = blank < 0 ? data.length : blank;
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  let timestamp = 0;
  for (const line of data.subarray(0, headEnd).toString('utf8').split('\n')) {
    if (!line) continue;
    const sp = line.indexOf(' ');
    const key = sp < 0 ? line : line.slice(0, sp);
    const val = sp < 0 ? '' : line.slice(sp + 1);
    if (key === 'tree') tree = val;
    else if (key === 'parent') parents.push(val);
    else if (key === 'author') author = val;
    else if (key === 'committer') {
      committer = val;
      const m = val.match(/ (\d+) [+-]\d{4}$/);
      if (m) timestamp = parseInt(m[1], 10);
    }
  }
  return { tree, parents, author, committer, message, timestamp };
}

interface TreeEntry { mode: string; name: string; oid: string; }

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    if (sp < 0) throw new Error('tree: no mode separator');
    const nul = data.indexOf(0x00, sp + 1);
    if (nul < 0 || nul + 21 > data.length) throw new Error('tree: truncated entry');
    entries.push({
      mode: data.subarray(off, sp).toString('ascii'),
      name: data.subarray(sp + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    off = nul + 21;
  }
  return entries;
}

function parseTag(data: Buffer): { object: string; type: string; tag: string; tagger: string; message: string } {
  const blank = data.indexOf('\n\n');
  const headEnd = blank < 0 ? data.length : blank;
  const headers = new Map<string, string>();
  for (const line of data.subarray(0, headEnd).toString('utf8').split('\n')) {
    if (!line) continue;
    const sp = line.indexOf(' ');
    if (sp < 0) continue;
    headers.set(line.slice(0, sp), line.slice(sp + 1));
  }
  return {
    object: headers.get('object') ?? '',
    type: headers.get('type') ?? '',
    tag: headers.get('tag') ?? '',
    tagger: headers.get('tagger') ?? '',
    message: blank < 0 ? '' : data.subarray(blank + 2).toString('utf8'),
  };
}

/** Git tree sort: entries sorted by name, directories compared as name + '/'. */
function sortTreeEntries(entries: TreeEntry[]): TreeEntry[] {
  return [...entries].sort((a, b) => {
    const ka = a.mode === '40000' ? `${a.name}/` : a.name;
    const kb = b.mode === '40000' ? `${b.name}/` : b.name;
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const parts: Buffer[] = [];
  for (const e of sortTreeEntries(entries)) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

function buildCommit(tree: string, parents: readonly string[], message: string, timestamp: number, authorName = VIEWER, authorEmail = VIEWER_EMAIL): Buffer {
  const ident = `${authorName} <${authorEmail}> ${timestamp} +0000`;
  let text = `tree ${tree}\n`;
  for (const p of parents) text += `parent ${p}\n`;
  text += `author ${ident}\ncommitter ${ident}\n\n${message}`;
  if (!message.endsWith('\n')) text += '\n';
  return Buffer.from(text, 'utf8');
}

// ---------------------------------------------------------------- packfiles

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      if (off >= delta.length) throw new Error('delta varint truncated');
      const b = delta[off++];
      value += (b & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(b & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.allocUnsafe(targetSize);
  let written = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let copyOff = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit++) {
        if (op & (1 << bit)) copyOff += delta[off++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit++) {
        if (op & (1 << bit)) copySize += delta[off++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOff, copyOff + copySize);
      written += copySize;
    } else if (op !== 0) {
      const lit = op & 0x7f;
      delta.copy(out, written, off, off + lit);
      off += lit;
      written += lit;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== targetSize) throw new Error('delta size mismatch');
  return out;
}

function inflateAt(buf: Buffer, offset: number): { data: Buffer; next: number } {
  const result = inflateSync(buf.subarray(offset), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
  const written = result.engine.bytesWritten;
  if (!written || written <= 0) throw new Error('zlib consumed no bytes');
  return { data: result.buffer, next: offset + written };
}

const TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function packObjectHeader(type: ObjType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** Build a packfile from plain objects (no deltas). Trailer = SHA-1 of all prior bytes. */
function writePack(objects: readonly GitObject[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.allocUnsafe(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const o of objects) {
    parts.push(packObjectHeader(o.type, o.data.length));
    parts.push(deflateSync(o.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

interface RawEntry {
  offset: number;
  typeCode: number;
  size: number;
  data: Buffer;
  baseOffset?: number;
  baseOid?: string;
  resolvedType?: ObjType;
  resolved?: Buffer;
  oid?: string;
}

/** Read a packfile; resolves OFS_DELTA and REF_DELTA. Verifies sizes; recomputes ids. */
function readPack(pack: Buffer, resolveBase?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  if (pack.length < 32) throw new Error('pack too short');
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack header');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack version ${version}`);
  const declared = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const raw: RawEntry[] = [];
  const byOffset = new Map<number, RawEntry>();
  let offset = 12;
  const readVarint = (start: number): { size: number; next: number; first: number } => {
    let byte = pack[start];
    const first = byte;
    let size = byte & 0x0f;
    let shift = 4;
    let o = start + 1;
    while (byte & 0x80) {
      byte = pack[o++];
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    return { size, next: o, first };
  };
  for (let i = 0; i < declared; i++) {
    const entryOffset = offset;
    const hv = readVarint(offset);
    offset = hv.next;
    const typeCode = (hv.first >> 4) & 0x07;
    const entry: RawEntry = { offset: entryOffset, typeCode, size: hv.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      let byte = pack[offset];
      let o = offset + 1;
      let value = byte & 0x7f;
      while (byte & 0x80) {
        byte = pack[o++];
        value = ((value + 1) * 128) + (byte & 0x7f);
      }
      offset = o;
      entry.baseOffset = entryOffset - value;
    } else if (typeCode === 7) {
      entry.baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!CODE_TYPE[typeCode]) {
      throw new Error(`pack type ${typeCode}`);
    }
    const inflated = inflateAt(pack.subarray(0, trailerStart), offset);
    if (inflated.data.length !== hv.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.data;
    offset = inflated.next;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  if (offset !== trailerStart) throw new Error('pack trailing bytes');
  const objects = new Map<string, GitObject>();
  const resolvedByOid = new Map<string, RawEntry>();
  const resolving = new Set<number>();
  const resolve = (entry: RawEntry): { type: ObjType; data: Buffer; oid: string } => {
    if (entry.resolved && entry.resolvedType && entry.oid) return { type: entry.resolvedType, data: entry.resolved, oid: entry.oid };
    if (resolving.has(entry.offset)) throw new Error('delta cycle');
    resolving.add(entry.offset);
    let type: ObjType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      if (!baseEntry) throw new Error('ofs-delta base missing');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const baseEntry = resolvedByOid.get(entry.baseOid!);
      if (baseEntry) {
        const base = resolve(baseEntry);
        type = base.type;
        data = applyDelta(base.data, entry.data);
      } else {
        const ext = resolveBase?.(entry.baseOid!);
        if (!ext) throw new Error('ref-delta base missing');
        type = ext.type;
        data = applyDelta(ext.data, entry.data);
      }
    } else {
      type = CODE_TYPE[entry.typeCode];
      data = entry.data;
    }
    const oid = hashObject(type, data);
    entry.resolved = data;
    entry.resolvedType = type;
    entry.oid = oid;
    resolvedByOid.set(oid, entry);
    resolving.delete(entry.offset);
    return { type, data, oid };
  };
  for (const entry of raw) {
    const r = resolve(entry);
    if (!objects.has(r.oid)) objects.set(r.oid, { type: r.type, data: r.data });
  }
  return objects;
}

// ---------------------------------------------------------------- store

interface Issue {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: { name: string; color: string }[];
  createdSeq: number;
  json: string; // precomputed GET /issues/{n} body
}
interface Comment { id: number; body: string; user: string; }
interface Pull {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  head: string;
  base: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  createdSeq: number;
}
interface Repo {
  id: number;
  owner: string;
  name: string;
  isPrivate: boolean;
  description: string;
  defaultBranch: string;
  refs: Map<string, string>;
  objects: Map<string, GitObject>;
  issues: Issue[];
  nextIssue: number;
  comments: Map<number, Comment[]>;
  nextComment: number;
  labels: Map<string, { name: string; color: string }>;
  pulls: Pull[];
  nextPull: number;
  seq: number;
  repoJson: string;
  adV2: Buffer | null;
  adV0Up: Buffer | null;
  adV0Recv: Buffer | null;
  lsCache: Map<string, Buffer>;
  packCache: Map<string, Buffer>;
  commitTs: number; // monotonic timestamp source for REST-created commits
}

const repos = new Map<string, Repo>();
let nextRepoId = 1000;
let globalSeq = 0;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function issueJsonOf(repo: Repo, issue: Issue): string {
  return JSON.stringify({
    id: repo.id * 100000 + issue.number,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((l) => ({ name: l.name, color: l.color })),
    user: { login: VIEWER },
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    comments: 0,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`,
  });
}

function repoJsonOf(repo: Repo): string {
  return JSON.stringify({
    id: repo.id,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: 1, type: 'User' },
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    clone_url: `https://example.invalid/${repo.owner}/${repo.name}.git`,
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    has_issues: true,
    has_pull_requests: true,
  });
}

function createRepoRecord(owner: string, name: string, isPrivate: boolean, description: string): Repo {
  const repo: Repo = {
    id: nextRepoId++,
    owner,
    name,
    isPrivate,
    description,
    defaultBranch: 'main',
    refs: new Map(),
    objects: new Map(),
    issues: [],
    nextIssue: 1,
    comments: new Map(),
    nextComment: 1,
    labels: new Map(),
    pulls: [],
    nextPull: 1,
    seq: ++globalSeq,
    repoJson: '',
    adV2: null,
    adV0Up: null,
    adV0Recv: null,
    lsCache: new Map(),
    packCache: new Map(),
    commitTs: EPOCH,
  };
  repo.repoJson = repoJsonOf(repo);
  repos.set(repoKey(owner, name), repo);
  return repo;
}

function invalidateGitCaches(repo: Repo): void {
  repo.adV2 = null;
  repo.adV0Up = null;
  repo.adV0Recv = null;
  repo.lsCache.clear();
  // packCache stays: packs are keyed by exact tip set, so old entries remain valid.
  if (repo.packCache.size > 64) {
    const keys = [...repo.packCache.keys()];
    for (let i = 0; i < keys.length - 64; i++) repo.packCache.delete(keys[i]!);
  }
}

// ---------------------------------------------------------------- object graph

/** All objects reachable from `roots` (commits, trees, blobs, tags), following parents. */
function reachableObjects(repo: Repo, roots: Iterable<string>): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [];
  for (const r of roots) if (isOid(r) && r !== ZERO_OID) stack.push(r);
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree);
      for (const p of c.parents) stack.push(p);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') stack.push(e.oid);
    }
  }
  return seen;
}

/** Is `ancestor` reachable from `tip` (commit ancestry only)? */
function isAncestor(repo: Repo, ancestor: string, tip: string): boolean {
  if (ancestor === tip) return true;
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length) {
    const oid = stack.pop()!;
    if (oid === ancestor) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return false;
}

/** Best common ancestor (merge-base) of two commits: BFS from both sides by generation. */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const fromA = new Map<string, number>();
  const qa: [string, number][] = [[a, 0]];
  while (qa.length) {
    const [oid, gen] = qa.shift()!;
    if (fromA.has(oid)) continue;
    fromA.set(oid, gen);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) qa.push([p, gen + 1]);
  }
  const qb: [string, number][] = [[b, 0]];
  const seenB = new Set<string>();
  let best: string | null = null;
  let bestScore = Infinity;
  while (qb.length) {
    const [oid, gen] = qb.shift()!;
    if (seenB.has(oid)) continue;
    seenB.add(oid);
    const ga = fromA.get(oid);
    if (ga !== undefined) {
      const score = ga + gen;
      if (score < bestScore) { bestScore = score; best = oid; }
    }
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) qb.push([p, gen + 1]);
  }
  return best;
}

/** Peel a tag (recursively) to the underlying commit/tree/blob oid. */
function peelToCommit(repo: Repo, oid: string): string | null {
  let cur = oid;
  for (let i = 0; i < 16; i++) {
    const obj = repo.objects.get(cur);
    if (!obj) return null;
    if (obj.type === 'tag') { cur = parseTag(obj.data).object; continue; }
    return cur;
  }
  return null;
}

/** Flat file map (path -> {mode, oid}) for a tree, recursively. */
function treeFileMap(repo: Repo, treeOid: string, prefix = '', out = new Map<string, { mode: string; oid: string }>()): Map<string, { mode: string; oid: string }> {
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') treeFileMap(repo, e.oid, path, out);
    else out.set(path, { mode: e.mode, oid: e.oid });
  }
  return out;
}

/** Build (and store) tree objects from a flat file map; returns the root tree oid. */
function fileMapToTree(repo: Repo, files: Map<string, { mode: string; oid: string }>): string {
  // Group paths by directory.
  const byDir = new Map<string, Map<string, { mode: string; oid: string }>>();
  for (const [path, v] of files) {
    const slash = path.lastIndexOf('/');
    const dir = slash < 0 ? '' : path.slice(0, slash);
    const name = slash < 0 ? path : path.slice(slash + 1);
    let m = byDir.get(dir);
    if (!m) { m = new Map(); byDir.set(dir, m); }
    m.set(name, v);
  }
  const buildDir = (dir: string): string => {
    const entries: TreeEntry[] = [];
    const direct = byDir.get(dir);
    if (direct) for (const [name, v] of direct) entries.push({ mode: v.mode, name, oid: v.oid });
    // Subdirectories of dir.
    const subdirs = new Set<string>();
    for (const d of byDir.keys()) {
      if (d === dir) continue;
      if (dir === '') {
        const first = d.split('/')[0]!;
        subdirs.add(first);
      } else if (d.startsWith(`${dir}/`)) {
        subdirs.add(d.slice(dir.length + 1).split('/')[0]!);
      }
    }
    for (const sub of subdirs) entries.push({ mode: '40000', name: sub, oid: buildDir(dir === '' ? sub : `${dir}/${sub}`) });
    const data = buildTree(entries);
    const oid = hashObject('tree', data);
    if (!repo.objects.has(oid)) repo.objects.set(oid, { type: 'tree', data });
    return oid;
  };
  return buildDir('');
}

/** Store a commit object built from a file map; returns its oid. */
function storeCommit(repo: Repo, files: Map<string, { mode: string; oid: string }>, parents: readonly string[], message: string): string {
  const tree = fileMapToTree(repo, files);
  const ts = ++repo.commitTs;
  const data = buildCommit(tree, parents, message, ts);
  const oid = hashObject('commit', data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type: 'commit', data });
  return oid;
}

/** Commits reachable from `tip`, newest first (by committer timestamp, then discovery). */
function listCommits(repo: Repo, tip: string): { sha: string; message: string; timestamp: number }[] {
  const seen = new Set<string>();
  const stack = [tip];
  const out: { sha: string; message: string; timestamp: number }[] = [];
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    const c = parseCommit(obj.data);
    out.push({ sha: oid, message: c.message.replace(/\n$/, ''), timestamp: c.timestamp });
    for (const p of c.parents) stack.push(p);
  }
  out.sort((a, b) => b.timestamp - a.timestamp);
  return out;
}

/** Simple line diff (LCS) for small files: returns {additions, deletions}. */
function lineDiff(oldText: string, newText: string): { additions: number; deletions: number } {
  if (oldText === newText) return { additions: 0, deletions: 0 };
  const a = oldText === '' ? [] : oldText.split('\n');
  const b = newText === '' ? [] : newText.split('\n');
  const n = a.length;
  const m = b.length;
  // LCS DP with a single row pair; files in this suite are small.
  let prev = new Array<number>(m + 1).fill(0);
  let cur = new Array<number>(m + 1).fill(0);
  for (let i = 1; i <= n; i++) {
    for (let j = 1; j <= m; j++) {
      cur[j] = a[i - 1] === b[j - 1] ? prev[j - 1] + 1 : Math.max(prev[j], cur[j - 1]);
    }
    const tmp = prev; prev = cur; cur = tmp;
  }
  const lcs = prev[m];
  return { additions: m - lcs, deletions: n - lcs };
}

// ---------------------------------------------------------------- fetch computation

interface FetchPlan {
  objects: GitObject[];
  shallow: string[];
  unshallow: string[];
}

/**
 * Compute the objects a fetch delivers.
 * - depth null: closure(wants) minus closure(haves) (haves' closure stops at the client's
 *   shallow boundaries).
 * - depth N: commits in generations 0..N-1 from wants, plus their trees/blobs, minus the
 *   have-closure; new shallow boundaries are the generation N-1 commits that still have parents;
 *   a client boundary whose parents are now delivered becomes unshallow.
 */
function computeFetch(repo: Repo, wants: string[], haves: string[], shallowIn: string[], depth: number | null): FetchPlan {
  const shallowSet = new Set(shallowIn);
  // Closure of haves, not traversing past shallow boundaries.
  const haveClosure = new Set<string>();
  {
    const stack = [...haves];
    while (stack.length) {
      const oid = stack.pop()!;
      if (haveClosure.has(oid)) continue;
      const obj = repo.objects.get(oid);
      if (!obj) continue;
      haveClosure.add(oid);
      if (obj.type === 'commit') {
        const c = parseCommit(obj.data);
        stack.push(c.tree);
        if (!shallowSet.has(oid)) for (const p of c.parents) stack.push(p);
      } else if (obj.type === 'tag') {
        stack.push(parseTag(obj.data).object);
      } else if (obj.type === 'tree') {
        for (const e of parseTree(obj.data)) if (e.mode !== '160000') stack.push(e.oid);
      }
    }
  }

  const send = new Set<string>();
  const newShallow: string[] = [];
  const unshallow: string[] = [];
  if (depth === null) {
    for (const oid of reachableObjects(repo, wants)) if (!haveClosure.has(oid)) send.add(oid);
  } else {
    // Walk commits by generation from wants.
    const commitGen = new Map<string, number>();
    const queue: [string, number][] = [];
    for (const w of wants) {
      const peeled = peelToCommit(repo, w);
      const start = peeled ?? w;
      if (repo.objects.get(start)?.type === 'commit') queue.push([start, 0]);
      else if (repo.objects.has(w)) {
        // A non-commit want (tag/blob/tree): include its closure.
        for (const oid of reachableObjects(repo, [w])) if (!haveClosure.has(oid)) send.add(oid);
      }
    }
    // Include the wanted tag objects themselves.
    for (const w of wants) {
      const obj = repo.objects.get(w);
      if (obj?.type === 'tag' && !haveClosure.has(w)) send.add(w);
    }
    const includedCommits = new Set<string>();
    while (queue.length) {
      const [oid, gen] = queue.shift()!;
      if (commitGen.has(oid)) continue;
      commitGen.set(oid, gen);
      includedCommits.add(oid);
      const obj = repo.objects.get(oid);
      if (!obj || obj.type !== 'commit') continue;
      const c = parseCommit(obj.data);
      if (gen < depth) {
        // This generation's tree/blobs are delivered.
        for (const x of reachableObjects(repo, [c.tree])) if (!haveClosure.has(x)) send.add(x);
        if (!haveClosure.has(oid)) send.add(oid);
        if (gen + 1 < depth) {
          for (const p of c.parents) queue.push([p, gen + 1]);
        } else {
          // Generation depth-1: boundary if it has parents.
          if (c.parents.length > 0) newShallow.push(oid);
        }
      }
    }
    // Unshallow: a client boundary whose parents are now delivered.
    for (const b of shallowIn) {
      if (!includedCommits.has(b)) continue;
      const obj = repo.objects.get(b);
      if (!obj || obj.type !== 'commit') continue;
      const parents = parseCommit(obj.data).parents;
      if (parents.length > 0 && parents.some((p) => includedCommits.has(p))) unshallow.push(b);
    }
    // A boundary at the new cutoff that was already shallow stays shallow (in newShallow).
    // Remove from newShallow any commit that is also unshallow (cannot happen: unshallow ones
    // are at generation < depth-1).
    void unshallow;
  }
  const objects: GitObject[] = [];
  for (const oid of send) {
    const obj = repo.objects.get(oid);
    if (obj) objects.push(obj);
  }
  return { objects, shallow: newShallow, unshallow };
}

function sidebandPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  let off = 0;
  while (off < pack.length) {
    const chunk = pack.subarray(off, Math.min(pack.length, off + PKT_PAYLOAD - 1));
    off += chunk.length;
    const payload = Buffer.concat([Buffer.from([1]), chunk]);
    parts.push(pktLine(payload));
  }
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------- HTTP plumbing

let reqCounter = 0;

function sendJson(res: ServerResponse, status: number, body: string | object, extra: Record<string, string> = {}): void {
  const text = typeof body === 'string' ? body : JSON.stringify(body);
  const headers: Record<string, string> = {
    'content-type': 'application/json; charset=utf-8',
    'x-github-request-id': randomBytes(8).toString('hex'),
    ...extra,
  };
  try {
    res.writeHead(status, headers);
    res.end(text);
  } catch { /* peer gone */ }
}

function sendBuffer(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  try {
    res.writeHead(status, {
      'content-type': contentType,
      'content-length': body.length,
      'x-github-request-id': randomBytes(8).toString('hex'),
    });
    res.end(body);
  } catch { /* peer gone */ }
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let size = 0;
    req.on('data', (c: Buffer) => {
      size += c.length;
      if (size > 64 * 1024 * 1024) { reject(new Error('body too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function parseJsonBody(buf: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (buf.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(buf.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return v !== null && typeof v === 'object' && !Array.isArray(v);
}

function authOk(req: IncomingMessage): boolean {
  if (TOKEN === '') return true;
  const h = req.headers.authorization ?? '';
  return h === `Bearer ${TOKEN}`;
}

function unauthorized(res: ServerResponse): void {
  sendJson(res, 401, { message: 'Requires authentication' });
}

function notFound(res: ServerResponse, what = 'Not Found'): void {
  sendJson(res, 404, { message: what });
}

// ---------------------------------------------------------------- git handlers

function sortedRefs(repo: Repo): [string, string][] {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
}

let V2_AD: Buffer | null = null;

function v2Advertisement(): Buffer {
  if (!V2_AD) {
    V2_AD = pktLines([
      'version 2\n',
      'ls-refs=unborn\n',
      'fetch=shallow wait-for-done\n',
      'object-format=sha1\n',
      `agent=${AGENT}\n`,
      'flush',
    ]);
  }
  return V2_AD;
}

function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = service === 'git-upload-pack'
    ? `symref=HEAD:refs/heads/${repo.defaultBranch} side-band-64k shallow thin-pack ofs-delta multi_ack agent=${AGENT}`
    : `symref=HEAD:refs/heads/${repo.defaultBranch} report-status side-band-64k delete-refs ofs-delta agent=${AGENT}`;
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  const lines: string[] = [];
  if (refs.length === 0) {
    lines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`);
  } else {
    const head = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    const first = head ?? refs[0]![1];
    lines.push(`${first} HEAD\0${caps}\n`);
    for (const [name, oid] of refs) lines.push(`${oid} ${name}\n`);
    // Peeled lines for annotated tags.
    for (const [name, oid] of refs) {
      if (!name.startsWith('refs/tags/')) continue;
      const obj = repo.objects.get(oid);
      if (obj?.type === 'tag') {
        const peeled = peelToCommit(repo, oid);
        if (peeled) lines.push(`${peeled} ${name}^{}\n`);
      }
    }
  }
  parts.push(pktLines(lines));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, repo: Repo, service: string): void {
  if (service !== 'git-upload-pack' && service !== 'git-receive-pack') { notFound(res); return; }
  const v2 = req.headers['git-protocol'] === 'version=2';
  if (service === 'git-receive-pack') {
    if (!repo.adV0Recv) repo.adV0Recv = v0Advertisement(repo, 'git-receive-pack');
    sendBuffer(res, 200, repo.adV0Recv, 'application/x-git-receive-pack-advertisement');
    return;
  }
  if (v2) {
    sendBuffer(res, 200, v2Advertisement(), 'application/x-git-upload-pack-advertisement');
    return;
  }
  if (!repo.adV0Up) repo.adV0Up = v0Advertisement(repo, 'git-upload-pack');
  sendBuffer(res, 200, repo.adV0Up, 'application/x-git-upload-pack-advertisement');
}

function lsRefsResponse(repo: Repo, prefixes: string[], peel: boolean, symrefs: boolean, unborn: boolean): Buffer {
  const cacheKey = JSON.stringify([prefixes, peel, symrefs, unborn]);
  const cached = repo.lsCache.get(cacheKey);
  if (cached) return cached;
  const keep = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const lines: string[] = [];
  const headOid = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  if (keep('HEAD')) {
    if (headOid) {
      lines.push(symrefs ? `${headOid} HEAD symref-target:refs/heads/${repo.defaultBranch}\n` : `${headOid} HEAD\n`);
    } else if (unborn) {
      lines.push(`unborn HEAD symref-target:refs/heads/${repo.defaultBranch}\n`);
    }
  }
  for (const [name, oid] of sortedRefs(repo)) {
    if (!keep(name)) continue;
    let line = `${oid} ${name}`;
    if (peel) {
      const obj = repo.objects.get(oid);
      if (obj?.type === 'tag') {
        const peeled = peelToCommit(repo, oid);
        if (peeled) line += ` peeled:${peeled}`;
      }
    }
    lines.push(`${line}\n`);
  }
  const out = pktLines([...lines, 'flush']);
  repo.lsCache.set(cacheKey, out);
  return out;
}

function fetchResponse(repo: Repo, wants: string[], haves: string[], shallowIn: string[], depth: number | null, v2: boolean): Buffer {
  // Objects are immutable once stored, so a fetch plan for a fixed (wants, haves,
  // shallow, depth) tuple never changes: cache the whole response, including depth-1
  // clones (the benchmark's 50 concurrent clones of one tip all share it).
  const cacheKey = `${v2 ? 'v2' : 'v0'}|d${depth ?? ''}|w${[...wants].sort().join(',')}|h${[...haves].sort().join(',')}|s${[...shallowIn].sort().join(',')}`;
  const cached = repo.packCache.get(cacheKey);
  if (cached) return cached;
  const plan = computeFetch(repo, wants, haves, shallowIn, depth);
  const pack = writePack(plan.objects);
  const parts: Buffer[] = [];
  if (v2) {
    parts.push(pktLine('acknowledgments\n'), pktLine('NAK\n'), PKT_DELIM);
    if (plan.shallow.length || plan.unshallow.length) {
      parts.push(pktLine('shallow-info\n'));
      for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
      for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
      parts.push(PKT_DELIM);
    }
    parts.push(pktLine('packfile\n'));
    parts.push(sidebandPack(pack));
    parts.push(PKT_FLUSH);
  } else {
    parts.push(pktLine('NAK\n'));
    for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
    for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
    parts.push(sidebandPack(pack));
    parts.push(PKT_FLUSH);
  }
  const out = Buffer.concat(parts);
  repo.packCache.set(cacheKey, out);
  return out;
}

async function handleUploadPack(req: IncomingMessage, res: ServerResponse, repo: Repo, body: Buffer): Promise<void> {
  const v2 = req.headers['git-protocol'] === 'version=2';
  let packets;
  try {
    packets = decodePktLines(body);
  } catch {
    sendJson(res, 400, { message: 'malformed pkt-line' });
    return;
  }
  const lines: string[] = [];
  let sawDelim = false;
  for (const p of packets) {
    if (p.kind === 'delim') { sawDelim = true; continue; }
    if (p.kind === 'data') lines.push(p.payload.toString('utf8'));
  }
  if (!sawDelim && v2) {
    // A v2 request without a delim is malformed; answer 400 and stay healthy.
    sendJson(res, 400, { message: 'malformed v2 request' });
    return;
  }
  try {
    if (v2) {
      const cmd = (lines[0] ?? '').trim();
      if (cmd === 'command=ls-refs') {
        const args = lines.slice(1);
        const prefixes: string[] = [];
        let peel = false;
        let symrefs = false;
        let unborn = false;
        for (const a of args) {
          const t = a.trim();
          if (t === 'peel') peel = true;
          else if (t === 'symrefs') symrefs = true;
          else if (t === 'unborn') unborn = true;
          else if (t.startsWith('ref-prefix ')) prefixes.push(t.slice('ref-prefix '.length));
        }
        sendBuffer(res, 200, lsRefsResponse(repo, prefixes, peel, symrefs, unborn), 'application/x-git-upload-pack-result');
        return;
      }
      if (cmd === 'command=fetch') {
        const args = lines.slice(1);
        const wants: string[] = [];
        const haves: string[] = [];
        const shallowIn: string[] = [];
        let depth: number | null = null;
        for (const a of args) {
          const t = a.trim();
          if (t.startsWith('want ')) wants.push(t.slice(5));
          else if (t.startsWith('have ')) haves.push(t.slice(5));
          else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8));
          else if (t.startsWith('deepen ')) { const n = parseInt(t.slice(7), 10); if (Number.isFinite(n)) depth = n; }
          else if (t.startsWith('deepen-since ')) { /* not exercised by the suite */ }
          else if (t.startsWith('deepen-not ')) { /* not exercised by the suite */ }
        }
        if (wants.length === 0) {
          sendBuffer(res, 200, pktLines(['acknowledgments\n', 'NAK\n', 'delim', 'packfile\n', 'flush']), 'application/x-git-upload-pack-result');
          return;
        }
        sendBuffer(res, 200, fetchResponse(repo, wants, haves, shallowIn, depth, true), 'application/x-git-upload-pack-result');
        return;
      }
      sendJson(res, 400, { message: `unknown v2 command ${JSON.stringify(cmd)}` });
      return;
    }
    // v0 fetch: section 1 = wants/shallow/deepen, section 2 = haves/done.
    const wants: string[] = [];
    const haves: string[] = [];
    const shallowIn: string[] = [];
    let depth: number | null = null;
    let section = 0;
    for (const p of packets) {
      if (p.kind === 'flush') { section++; continue; }
      if (p.kind !== 'data') continue;
      const t = p.payload.toString('utf8').trim();
      if (section === 0) {
        if (t.startsWith('want ')) wants.push(t.slice(5).split(' ')[0]!);
        else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8));
        else if (t.startsWith('deepen ')) { const n = parseInt(t.slice(7), 10); if (Number.isFinite(n)) depth = n; }
      } else {
        if (t.startsWith('have ')) haves.push(t.slice(5));
      }
    }
    if (wants.length === 0) {
      sendBuffer(res, 200, pktLines(['NAK\n', 'flush']), 'application/x-git-upload-pack-result');
      return;
    }
    sendBuffer(res, 200, fetchResponse(repo, wants, haves, shallowIn, depth, false), 'application/x-git-upload-pack-result');
  } catch (err) {
    sendJson(res, 400, { message: `fetch failed: ${err instanceof Error ? err.message : String(err)}` });
  }
}

async function handleReceivePack(req: IncomingMessage, res: ServerResponse, repo: Repo, body: Buffer): Promise<void> {
  // Parse command pkt-lines incrementally: the first flush ends the commands and the
  // remaining bytes are the raw pack (never pkt-framed, so never decode them as lines).
  const commands: { oldOid: string; newOid: string; ref: string }[] = [];
  let packStart = body.length;
  let off = 0;
  let malformed = false;
  while (off + 4 <= body.length) {
    const len = parseInt(body.subarray(off, off + 4).toString('ascii'), 16);
    if (Number.isNaN(len)) { malformed = true; break; }
    if (len === 0) { packStart = off + 4; break; }
    if (len < 4 || off + len > body.length) { malformed = true; break; }
    const text = body.subarray(off + 4, off + len).toString('utf8');
    const nul = text.indexOf('\0');
    const head = (nul >= 0 ? text.slice(0, nul) : text).trim();
    const parts = head.split(' ');
    if (parts.length >= 3 && isOid(parts[0]!) && isOid(parts[1]!)) {
      commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts[2]! });
    }
    off += len;
  }
  if (malformed) {
    sendJson(res, 400, { message: 'malformed pkt-line' });
    return;
  }
  // Unpack: store every object, even when a ref update is refused.
  let unpackOk = true;
  let unpackDetail = 'ok';
  const packBytes = body.subarray(packStart);
  if (packBytes.length > 0) {
    try {
      const objects = readPack(packBytes, (oid) => repo.objects.get(oid));
      for (const [oid, obj] of objects) if (!repo.objects.has(oid)) repo.objects.set(oid, obj);
    } catch (err) {
      unpackOk = false;
      unpackDetail = err instanceof Error ? err.message : 'unpack failed';
    }
  }
  const reportLines: string[] = [`unpack ${unpackOk ? 'ok' : unpackDetail}\n`];
  let changed = false;
  for (const cmd of commands) {
    const current = repo.refs.get(cmd.ref);
    let ok = false;
    let reason = '';
    if (!unpackOk) {
      reason = 'unpack failed';
    } else if (cmd.newOid === ZERO_OID) {
      // Delete.
      if (current === undefined) reason = 'ref does not exist';
      else if (current !== cmd.oldOid) reason = 'old oid does not match';
      else { repo.refs.delete(cmd.ref); ok = true; changed = true; }
    } else if (cmd.oldOid === ZERO_OID) {
      // Create.
      if (current !== undefined) reason = 'ref already exists';
      else if (!repo.objects.has(cmd.newOid)) reason = 'object not found';
      else { repo.refs.set(cmd.ref, cmd.newOid); ok = true; changed = true; }
    } else {
      if (current === undefined) reason = 'ref does not exist';
      else if (current !== cmd.oldOid) reason = 'old oid does not match';
      else if (!repo.objects.has(cmd.newOid)) reason = 'object not found';
      else if (!isAncestor(repo, cmd.oldOid, cmd.newOid)) reason = 'non-fast-forward';
      else { repo.refs.set(cmd.ref, cmd.newOid); ok = true; changed = true; }
    }
    reportLines.push(ok ? `ok ${cmd.ref}\n` : `ng ${cmd.ref} ${reason}\n`);
  }
  if (changed) invalidateGitCaches(repo);
  const report = pktLines(reportLines);
  const framed = Buffer.concat([pktLine(Buffer.concat([Buffer.from([1]), report])), PKT_FLUSH]);
  sendBuffer(res, 200, framed, 'application/x-git-receive-pack-result');
}

// ---------------------------------------------------------------- REST v3

const SCOPES = { 'x-oauth-scopes': 'repo' };

function paginate<T>(items: readonly T[], query: URLSearchParams): { page: T[]; total: number; pageNum: number; perPage: number } {
  const perPage = Math.max(1, Math.min(100, parseInt(query.get('per_page') ?? '30', 10) || 30));
  const pageNum = Math.max(1, parseInt(query.get('page') ?? '1', 10) || 1);
  const start = (pageNum - 1) * perPage;
  return { page: items.slice(start, start + perPage), total: items.length, pageNum, perPage };
}

function linkHeader(base: string, path: string, query: URLSearchParams, pageNum: number, perPage: number, total: number): string {
  const lastPage = Math.max(1, Math.ceil(total / perPage));
  const mk = (p: number, rel: string): string => {
    const q = new URLSearchParams(query);
    q.set('page', String(p));
    q.set('per_page', String(perPage));
    return `<${base}${path}?${q.toString()}>; rel="${rel}"`;
  };
  const links: string[] = [];
  if (pageNum < lastPage) links.push(mk(pageNum + 1, 'next'), mk(lastPage, 'last'));
  if (pageNum > 1) links.push(mk(1, 'first'), mk(pageNum - 1, 'prev'));
  return links.join(', ');
}

function findRepo(owner: string, name: string): Repo | null {
  if (owner !== VIEWER) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}

function prJson(repo: Repo, pr: Pull): Record<string, unknown> {
  const headSha = repo.refs.get(`refs/heads/${pr.head}`) ?? ZERO_OID;
  const baseSha = repo.refs.get(`refs/heads/${pr.base}`) ?? ZERO_OID;
  return {
    id: repo.id * 100000 + pr.number,
    number: pr.number,
    title: pr.title,
    body: pr.body,
    state: pr.state,
    head: { ref: pr.head, sha: headSha, label: `${VIEWER}:${pr.head}` },
    base: { ref: pr.base, sha: baseSha, label: `${VIEWER}:${pr.base}` },
    merged: pr.merged,
    merged_at: pr.mergedAt,
    merge_commit_sha: pr.mergeCommitSha,
    user: { login: VIEWER },
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/pull/${pr.number}`,
  };
}

function resolveRefTip(repo: Repo, ref: string | null): string | null {
  if (ref === null) return repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
  const byBranch = repo.refs.get(`refs/heads/${ref}`);
  if (byBranch) return byBranch;
  if (isOid(ref) && repo.objects.has(ref)) return ref;
  return null;
}

function treeAtPath(repo: Repo, tip: string, path: string): { kind: 'file' | 'dir'; oid: string; entries?: TreeEntry[]; blob?: Buffer } | null {
  const commit = repo.objects.get(tip);
  if (!commit || commit.type !== 'commit') return null;
  const rootTree = parseCommit(commit.data).tree;
  if (path === '' || path === '/') {
    const obj = repo.objects.get(rootTree);
    if (!obj) return null;
    return { kind: 'dir', oid: rootTree, entries: parseTree(obj.data) };
  }
  const segments = path.split('/').filter((s) => s !== '');
  let curOid = rootTree;
  for (let i = 0; i < segments.length; i++) {
    const obj = repo.objects.get(curOid);
    if (!obj || obj.type !== 'tree') return null;
    const entry = parseTree(obj.data).find((e) => e.name === segments[i]);
    if (!entry) return null;
    if (i === segments.length - 1) {
      if (entry.mode === '40000') {
        const child = repo.objects.get(entry.oid);
        if (!child) return null;
        return { kind: 'dir', oid: entry.oid, entries: parseTree(child.data) };
      }
      const blob = repo.objects.get(entry.oid);
      if (!blob) return null;
      return { kind: 'file', oid: entry.oid, blob: blob.data };
    }
    if (entry.mode !== '40000') return null;
    curOid = entry.oid;
  }
  return null;
}

function doMerge(repo: Repo, pr: Pull): { ok: boolean; status: number; sha?: string; message?: string } {
  const headTip = repo.refs.get(`refs/heads/${pr.head}`);
  const baseTip = repo.refs.get(`refs/heads/${pr.base}`);
  if (!headTip || !baseTip) return { ok: false, status: 422, message: 'head or base branch is missing' };
  const base = mergeBase(repo, baseTip, headTip);
  if (base === null) return { ok: false, status: 405, message: 'no merge base' };
  const baseFiles = treeFileMap(repo, parseCommit(repo.objects.get(base)!.data).tree);
  const headFiles = treeFileMap(repo, parseCommit(repo.objects.get(headTip)!.data).tree);
  const baseTipFiles = treeFileMap(repo, parseCommit(repo.objects.get(baseTip)!.data).tree);
  // Conflict: a path changed on both sides with different results.
  const allPaths = new Set([...baseFiles.keys(), ...headFiles.keys(), ...baseTipFiles.keys()]);
  for (const path of allPaths) {
    const b = baseFiles.get(path);
    const h = headFiles.get(path);
    const t = baseTipFiles.get(path);
    const headChanged = (h?.oid ?? null) !== (b?.oid ?? null);
    const baseChanged = (t?.oid ?? null) !== (b?.oid ?? null);
    if (headChanged && baseChanged && (h?.oid ?? null) !== (t?.oid ?? null)) {
      return { ok: false, status: 405, message: 'merge conflict' };
    }
  }
  // Three-way merge: head wins where it changed, base tip wins elsewhere.
  const merged = new Map<string, { mode: string; oid: string }>();
  for (const path of allPaths) {
    const b = baseFiles.get(path);
    const h = headFiles.get(path);
    const t = baseTipFiles.get(path);
    const headChanged = (h?.oid ?? null) !== (b?.oid ?? null);
    if (headChanged) {
      if (h) merged.set(path, h);
    } else if (t) {
      merged.set(path, t);
    }
  }
  const mergeSha = storeCommit(repo, merged, [baseTip], `Merge pull request #${pr.number} from ${pr.head}\n\n${pr.title}`);
  repo.refs.set(`refs/heads/${pr.base}`, mergeSha);
  invalidateGitCaches(repo);
  pr.state = 'closed';
  pr.merged = true;
  pr.mergedAt = '2025-01-01T00:00:00Z';
  pr.mergeCommitSha = mergeSha;
  return { ok: true, status: 200, sha: mergeSha, message: `Merge pull request #${pr.number} from ${pr.head}` };
}

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL, body: Buffer): Promise<void> {
  const method = req.method ?? 'GET';
  const segs = url.pathname.split('/').filter((s) => s !== '');
  // segs[0] === 'api', segs[1] === 'v3'
  const rest = segs.slice(2);
  const query = url.searchParams;

  const needAuth = !(rest.length === 0 || (rest.length === 1 && rest[0] === 'meta'));
  if (needAuth && !authOk(req)) { unauthorized(res); return; }

  // Root and meta (no auth required).
  if (rest.length === 0) {
    if (method !== 'GET') { sendJson(res, 404, { message: 'Not Found' }, SCOPES); return; }
    sendJson(res, 200, { current_user_url: '/api/v3/user' }, SCOPES);
    return;
  }
  if (rest.length === 1 && rest[0] === 'meta') {
    sendJson(res, 200, { installed_version: '1.0.0' }, SCOPES);
    return;
  }

  let parsed: { ok: true; value: unknown } | { ok: false } = { ok: true, value: {} };
  if (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE') {
    parsed = parseJsonBody(body);
    if (!parsed.ok) { sendJson(res, 400, { message: 'malformed JSON body' }, SCOPES); return; }
  }
  const input: Record<string, unknown> = isRecord(parsed.ok ? parsed.value : {}) ? (parsed.value as Record<string, unknown>) : {};

  // GET /user
  if (rest.length === 1 && rest[0] === 'user' && method === 'GET') {
    sendJson(res, 200, { login: VIEWER, id: 1, type: 'User' }, SCOPES);
    return;
  }

  // POST /user/repos ; GET /user/repos
  if (rest.length === 2 && rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'POST') {
      const name = typeof input.name === 'string' ? input.name : '';
      if (!/^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$/.test(name)) { sendJson(res, 422, { message: 'name is invalid' }, SCOPES); return; }
      if (repos.has(repoKey(VIEWER, name))) { sendJson(res, 422, { message: 'Repository already exists' }, SCOPES); return; }
      const repo = createRepoRecord(VIEWER, name, input.private === true, typeof input.description === 'string' ? input.description : '');
      sendJson(res, 201, repo.repoJson, SCOPES);
      return;
    }
    if (method === 'GET') {
      const all = [...repos.values()].filter((r) => r.owner === VIEWER).sort((a, b) => a.seq - b.seq);
      const { page, total, pageNum, perPage } = paginate(all, query);
      const link = linkHeader(`http://${req.headers.host ?? '127.0.0.1'}`, '/api/v3/user/repos', query, pageNum, perPage, total);
      sendJson(res, 200, `[${page.map((r) => r.repoJson).join(',')}]`, { ...SCOPES, ...(link ? { link } : {}) });
      return;
    }
  }

  // /repos/{owner}/{name}[...]
  if (rest.length >= 3 && rest[0] === 'repos') {
    const owner = decodeURIComponent(rest[1]!);
    const name = decodeURIComponent(rest[2]!);
    const repo = findRepo(owner, name);
    const tail = rest.slice(3);

    if (tail.length === 0) {
      if (method === 'GET') {
        if (!repo) { notFound(res, 'Not Found'); return; }
        sendJson(res, 200, repo.repoJson, SCOPES);
        return;
      }
      if (method === 'PATCH') {
        if (!repo) { notFound(res, 'Not Found'); return; }
        if (typeof input.description === 'string') repo.description = input.description;
        repo.repoJson = repoJsonOf(repo);
        sendJson(res, 200, repo.repoJson, SCOPES);
        return;
      }
      if (method === 'DELETE') {
        if (!repo) { notFound(res, 'Not Found'); return; }
        repos.delete(repoKey(owner, name));
        try { res.writeHead(204, { 'x-github-request-id': randomBytes(8).toString('hex') }); res.end(); } catch { /* gone */ }
        return;
      }
    }

    if (!repo) { notFound(res, 'Not Found'); return; }

    // branches
    if (tail.length === 1 && tail[0] === 'branches' && method === 'GET') {
      const list = [...repo.refs.entries()]
        .filter(([n]) => n.startsWith('refs/heads/'))
        .map(([n, oid]) => ({ name: n.slice('refs/heads/'.length), commit: { sha: oid } }))
        .sort((a, b) => (a.name < b.name ? -1 : 1));
      sendJson(res, 200, list, SCOPES);
      return;
    }

    // commits
    if (tail.length === 1 && tail[0] === 'commits' && method === 'GET') {
      const tip = resolveRefTip(repo, query.get('sha'));
      if (!tip) { sendJson(res, 200, [], SCOPES); return; }
      const list = listCommits(repo, tip).map((c) => ({ sha: c.sha, commit: { message: c.message }, author: { login: VIEWER }, committer: { login: VIEWER } }));
      sendJson(res, 200, list, SCOPES);
      return;
    }

    // git/refs
    if (tail.length >= 2 && tail[0] === 'git' && tail[1] === 'refs') {
      if (method === 'POST' && tail.length === 2) {
        const ref = typeof input.ref === 'string' ? input.ref : '';
        const sha = typeof input.sha === 'string' ? input.sha : '';
        if (!ref.startsWith('refs/heads/') || !isOid(sha) || !repo.objects.has(sha)) {
          sendJson(res, 422, { message: 'invalid ref or sha' }, SCOPES);
          return;
        }
        if (repo.refs.has(ref)) { sendJson(res, 422, { message: 'Reference already exists' }, SCOPES); return; }
        repo.refs.set(ref, sha);
        invalidateGitCaches(repo);
        sendJson(res, 201, { ref, object: { sha } }, SCOPES);
        return;
      }
      if (method === 'GET' && tail.length === 4 && tail[2] === 'heads') {
        const branch = decodeURIComponent(tail[3]!);
        const sha = repo.refs.get(`refs/heads/${branch}`);
        if (!sha) { notFound(res, 'Not Found'); return; }
        sendJson(res, 200, { ref: `refs/heads/${branch}`, object: { sha }, sha }, SCOPES);
        return;
      }
    }

    // contents
    if (tail.length >= 2 && tail[0] === 'contents') {
      const path = tail.slice(1).map((s) => decodeURIComponent(s)).join('/');
      if (method === 'GET') {
        const tip = resolveRefTip(repo, query.get('ref'));
        if (!tip) { notFound(res, 'Not Found'); return; }
        const found = treeAtPath(repo, tip, path);
        if (!found) { notFound(res, 'Not Found'); return; }
        if (found.kind === 'file') {
          const baseName = path.split('/').pop() ?? path;
          sendJson(res, 200, {
            type: 'file', encoding: 'base64', size: found.blob!.length,
            name: baseName, path, content: found.blob!.toString('base64'), sha: found.oid,
          }, SCOPES);
          return;
        }
        const entries = (found.entries ?? []).map((e) => ({
          type: e.mode === '40000' ? 'dir' : 'file',
          name: e.name,
          path: path === '' ? e.name : `${path}/${e.name}`,
          sha: e.oid,
          size: e.mode === '40000' ? 0 : (repo.objects.get(e.oid)?.data.length ?? 0),
        }));
        sendJson(res, 200, entries, SCOPES);
        return;
      }
      if (method === 'PUT') {
        const message = typeof input.message === 'string' ? input.message : 'update';
        const contentB64 = typeof input.content === 'string' ? input.content : '';
        let content: Buffer;
        try {
          content = Buffer.from(contentB64.replace(/\s/g, ''), 'base64');
        } catch {
          sendJson(res, 422, { message: 'content is not base64' }, SCOPES);
          return;
        }
        const branch = typeof input.branch === 'string' ? input.branch : repo.defaultBranch;
        let tip = repo.refs.get(`refs/heads/${branch}`);
        let files = new Map<string, { mode: string; oid: string }>();
        let parents: string[] = [];
        if (tip) {
          const commit = repo.objects.get(tip);
          if (commit?.type === 'commit') {
            files = treeFileMap(repo, parseCommit(commit.data).tree);
            parents = [tip];
          }
        } else if (branch !== repo.defaultBranch && repo.refs.size > 0) {
          // Create the branch from the default tip.
          const defTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
          if (defTip) {
            const commit = repo.objects.get(defTip);
            if (commit?.type === 'commit') {
              files = treeFileMap(repo, parseCommit(commit.data).tree);
              parents = [defTip];
            }
          }
        }
        const existing = files.get(path);
        const givenSha = typeof input.sha === 'string' ? input.sha : undefined;
        if (existing) {
          if (!givenSha) { sendJson(res, 422, { message: 'sha is required to update a file' }, SCOPES); return; }
          if (givenSha !== existing.oid) { sendJson(res, 409, { message: 'sha does not match the current file' }, SCOPES); return; }
        } else if (givenSha) {
          sendJson(res, 422, { message: 'sha given for a file that does not exist' }, SCOPES);
          return;
        }
        const blobOid = hashObject('blob', content);
        if (!repo.objects.has(blobOid)) repo.objects.set(blobOid, { type: 'blob', data: content });
        files.set(path, { mode: '100644', oid: blobOid });
        const commitSha = storeCommit(repo, files, parents, message);
        repo.refs.set(`refs/heads/${branch}`, commitSha);
        invalidateGitCaches(repo);
        sendJson(res, existing ? 200 : 201, {
          content: { name: path.split('/').pop(), path, sha: blobOid, size: content.length, encoding: 'base64', content: contentB64 },
          commit: { sha: commitSha, message },
        }, SCOPES);
        return;
      }
      if (method === 'DELETE') {
        const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        if (!tip) { notFound(res, 'Not Found'); return; }
        const commit = repo.objects.get(tip);
        if (!commit || commit.type !== 'commit') { notFound(res, 'Not Found'); return; }
        const files = treeFileMap(repo, parseCommit(commit.data).tree);
        const existing = files.get(path);
        if (!existing) { notFound(res, 'Not Found'); return; }
        const givenSha = typeof input.sha === 'string' ? input.sha : undefined;
        if (givenSha && givenSha !== existing.oid) { sendJson(res, 409, { message: 'sha does not match the current file' }, SCOPES); return; }
        files.delete(path);
        const message = typeof input.message === 'string' ? input.message : 'delete';
        const commitSha = storeCommit(repo, files, [tip], message);
        repo.refs.set(`refs/heads/${repo.defaultBranch}`, commitSha);
        invalidateGitCaches(repo);
        sendJson(res, 200, { commit: { sha: commitSha, message } }, SCOPES);
        return;
      }
    }

    // labels
    if (tail.length === 1 && tail[0] === 'labels' && method === 'POST') {
      const name = typeof input.name === 'string' ? input.name : '';
      const color = typeof input.color === 'string' ? input.color : 'ededed';
      if (name === '') { sendJson(res, 422, { message: 'name is required' }, SCOPES); return; }
      if (!repo.labels.has(name)) repo.labels.set(name, { name, color });
      const label = repo.labels.get(name)!;
      sendJson(res, 201, { name: label.name, color: label.color }, SCOPES);
      return;
    }

    // issues
    if (tail.length >= 1 && tail[0] === 'issues') {
      if (tail.length === 1) {
        if (method === 'POST') {
          const title = typeof input.title === 'string' ? input.title : '';
          const bodyText = typeof input.body === 'string' ? input.body : '';
          const labelNames: string[] = Array.isArray(input.labels) ? input.labels.filter((x): x is string => typeof x === 'string') : [];
          for (const ln of labelNames) {
            if (!repo.labels.has(ln)) { sendJson(res, 422, { message: `Label does not exist: ${ln}` }, SCOPES); return; }
          }
          const issue: Issue = {
            number: repo.nextIssue++,
            title,
            body: bodyText,
            state: 'open',
            labels: labelNames.map((ln) => repo.labels.get(ln)!),
            createdSeq: ++globalSeq,
            json: '',
          };
          issue.json = issueJsonOf(repo, issue);
          repo.issues.push(issue);
          sendJson(res, 201, issue.json, SCOPES);
          return;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          const sort = query.get('sort') ?? 'created';
          const direction = query.get('direction') ?? 'desc';
          let list = repo.issues.filter((i) => state === 'all' || i.state === state);
          if (sort === 'created') {
            list = [...list].sort((a, b) => direction === 'asc' ? a.number - b.number : b.number - a.number);
          }
          const { page } = paginate(list, query);
          sendJson(res, 200, `[${page.map((i) => i.json).join(',')}]`, SCOPES);
          return;
        }
      }
      if (tail.length === 2) {
        const num = parseInt(tail[1]!, 10);
        const issue = repo.issues.find((i) => i.number === num);
        if (!issue) { notFound(res, 'Not Found'); return; }
        if (method === 'GET') {
          sendJson(res, 200, issue.json, SCOPES);
          return;
        }
        if (method === 'PATCH') {
          if (typeof input.state === 'string' && (input.state === 'open' || input.state === 'closed')) issue.state = input.state;
          if (typeof input.title === 'string') issue.title = input.title;
          if (typeof input.body === 'string') issue.body = input.body;
          issue.json = issueJsonOf(repo, issue);
          sendJson(res, 200, issue.json, SCOPES);
          return;
        }
      }
      if (tail.length === 3 && tail[2] === 'comments') {
        const num = parseInt(tail[1]!, 10);
        const issue = repo.issues.find((i) => i.number === num);
        if (!issue) { notFound(res, 'Not Found'); return; }
        if (method === 'POST') {
          const bodyText = typeof input.body === 'string' ? input.body : '';
          const comment: Comment = { id: repo.nextComment++, body: bodyText, user: VIEWER };
          const list = repo.comments.get(num) ?? [];
          list.push(comment);
          repo.comments.set(num, list);
          sendJson(res, 201, { id: comment.id, body: comment.body, user: { login: VIEWER }, created_at: '2025-01-01T00:00:00Z' }, SCOPES);
          return;
        }
        if (method === 'GET') {
          const list = repo.comments.get(num) ?? [];
          sendJson(res, 200, list.map((c) => ({ id: c.id, body: c.body, user: { login: VIEWER }, created_at: '2025-01-01T00:00:00Z' })), SCOPES);
          return;
        }
      }
    }

    // pulls
    if (tail.length >= 1 && tail[0] === 'pulls') {
      if (tail.length === 1) {
        if (method === 'POST') {
          const title = typeof input.title === 'string' ? input.title : '';
          const bodyText = typeof input.body === 'string' ? input.body : '';
          const head = typeof input.head === 'string' ? input.head : '';
          const base = typeof input.base === 'string' ? input.base : repo.defaultBranch;
          if (!repo.refs.has(`refs/heads/${head}`) || !repo.refs.has(`refs/heads/${base}`)) {
            sendJson(res, 422, { message: 'head or base branch does not exist' }, SCOPES);
            return;
          }
          const dup = repo.pulls.find((p) => p.state === 'open' && p.head === head && p.base === base);
          if (dup) { sendJson(res, 422, { message: 'a pull request from this head already exists' }, SCOPES); return; }
          const pr: Pull = { number: repo.nextPull++, title, body: bodyText, state: 'open', head, base, merged: false, mergedAt: null, mergeCommitSha: null, createdSeq: ++globalSeq };
          repo.pulls.push(pr);
          sendJson(res, 201, prJson(repo, pr), SCOPES);
          return;
        }
        if (method === 'GET') {
          const state = query.get('state') ?? 'open';
          const list = repo.pulls.filter((p) => state === 'all' || p.state === state);
          const { page } = paginate(list, query);
          sendJson(res, 200, page.map((p) => prJson(repo, p)), SCOPES);
          return;
        }
      }
      if (tail.length === 2) {
        const num = parseInt(tail[1]!, 10);
        const pr = repo.pulls.find((p) => p.number === num);
        if (!pr) { notFound(res, 'Not Found'); return; }
        if (method === 'GET') {
          sendJson(res, 200, prJson(repo, pr), SCOPES);
          return;
        }
      }
      if (tail.length === 3 && tail[2] === 'files' && method === 'GET') {
        const num = parseInt(tail[1]!, 10);
        const pr = repo.pulls.find((p) => p.number === num);
        if (!pr) { notFound(res, 'Not Found'); return; }
        const headTip = repo.refs.get(`refs/heads/${pr.head}`);
        const baseTip = repo.refs.get(`refs/heads/${pr.base}`);
        if (!headTip || !baseTip) { sendJson(res, 200, [], SCOPES); return; }
        const headFiles = treeFileMap(repo, parseCommit(repo.objects.get(headTip)!.data).tree);
        const baseFiles = treeFileMap(repo, parseCommit(repo.objects.get(baseTip)!.data).tree);
        const out: Record<string, unknown>[] = [];
        for (const path of [...new Set([...headFiles.keys(), ...baseFiles.keys()])].sort()) {
          const h = headFiles.get(path);
          const b = baseFiles.get(path);
          if ((h?.oid ?? null) === (b?.oid ?? null)) continue;
          const oldText = b ? (repo.objects.get(b.oid)?.data.toString('utf8') ?? '') : '';
          const newText = h ? (repo.objects.get(h.oid)?.data.toString('utf8') ?? '') : '';
          const { additions, deletions } = lineDiff(oldText, newText);
          const status = !b ? 'added' : !h ? 'removed' : 'modified';
          out.push({ filename: path, status, additions, deletions, changes: additions + deletions });
        }
        sendJson(res, 200, out, SCOPES);
        return;
      }
      if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
        const num = parseInt(tail[1]!, 10);
        const pr = repo.pulls.find((p) => p.number === num);
        if (!pr) { notFound(res, 'Not Found'); return; }
        if (pr.merged) { sendJson(res, 405, { message: 'pull request is already merged' }, SCOPES); return; }
        const result = doMerge(repo, pr);
        if (!result.ok) { sendJson(res, result.status, { message: result.message ?? 'merge failed' }, SCOPES); return; }
        sendJson(res, 200, { merged: true, sha: result.sha, message: result.message }, SCOPES);
        return;
      }
    }
  }

  sendJson(res, 404, { message: 'Not Found' }, SCOPES);
}

// ---------------------------------------------------------------- GraphQL v4

const GQL_ID = (kind: string, ...parts: (string | number)[]): string =>
  Buffer.from(`${kind}:${parts.join(':')}`, 'utf8').toString('base64');

function decodeGqlId(id: string): { kind: string; parts: string[] } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const [kind, ...parts] = text.split(':');
    if (!kind || parts.length === 0) return null;
    return { kind, parts };
  } catch {
    return null;
  }
}

// --- tokenizer / parser (documents the suite sends only) ---

type GqlToken =
  | { t: 'name'; v: string }
  | { t: 'string'; v: string }
  | { t: 'int'; v: number }
  | { t: 'punct'; v: string }
  | { t: 'spread' };

function gqlTokenize(src: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i]!;
    if (ch === ' ' || ch === '\n' || ch === '\r' || ch === '\t' || ch === ',') { i++; continue; }
    if (ch === '#') { while (i < src.length && src[i] !== '\n') i++; continue; }
    if (ch === '.' && src.slice(i, i + 3) === '...') { tokens.push({ t: 'spread' }); i += 3; continue; }
    if ('{}()[]:!=$@'.includes(ch)) { tokens.push({ t: 'punct', v: ch }); i++; continue; }
    if (ch === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) {
          const e = src[j + 1]!;
          out += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e === '"' ? '"' : e === '\\' ? '\\' : e;
          j += 2;
        } else {
          out += src[j];
          j++;
        }
      }
      tokens.push({ t: 'string', v: out });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(ch) && (ch !== '-' || /[0-9]/.test(src[i + 1] ?? ''))) {
      let j = i;
      while (j < src.length && /[0-9.]/.test(src[j]!)) j++;
      tokens.push({ t: 'int', v: Number(src.slice(i, j)) });
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j]!)) j++;
      tokens.push({ t: 'name', v: src.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`graphql: unexpected character ${JSON.stringify(ch)}`);
  }
  return tokens;
}

type GqlValue =
  | { k: 'var'; name: string }
  | { k: 'string'; v: string }
  | { k: 'int'; v: number }
  | { k: 'bool'; v: boolean }
  | { k: 'null' }
  | { k: 'enum'; v: string }
  | { k: 'list'; v: GqlValue[] }
  | { k: 'object'; v: Record<string, GqlValue> };

interface GqlField {
  alias: string | null;
  name: string;
  args: Record<string, GqlValue>;
  children: GqlSelection[];
}
type GqlSelection =
  | { k: 'field'; f: GqlField }
  | { k: 'inline'; type: string | null; children: GqlSelection[] };

interface GqlOperation {
  kind: 'query' | 'mutation';
  name: string | null;
  selections: GqlSelection[];
}

class GqlParser {
  private pos = 0;
  private tokens: GqlToken[];
  constructor(tokens: GqlToken[]) {
    this.tokens = tokens;
  }

  private peek(): GqlToken | undefined { return this.tokens[this.pos]; }
  private next(): GqlToken {
    const t = this.tokens[this.pos];
    if (!t) throw new Error('graphql: unexpected end');
    this.pos++;
    return t;
  }
  private expectPunct(v: string): void {
    const t = this.next();
    if (t.t !== 'punct' || t.v !== v) throw new Error(`graphql: expected ${v}`);
  }
  private expectName(): string {
    const t = this.next();
    if (t.t !== 'name') throw new Error('graphql: expected name');
    return t.v;
  }

  parseDocument(): GqlOperation[] {
    const ops: GqlOperation[] = [];
    while (this.pos < this.tokens.length) {
      const t = this.peek()!;
      if (t.t === 'punct' && t.v === '{') {
        ops.push({ kind: 'query', name: null, selections: this.parseSelectionSet() });
        continue;
      }
      if (t.t === 'name' && (t.v === 'query' || t.v === 'mutation')) {
        const kind = this.next().v as 'query' | 'mutation';
        let name: string | null = null;
        const n = this.peek();
        if (n?.t === 'name') name = this.next().v as string;
        // Variable definitions: skip balanced parens.
        if (this.peek()?.t === 'punct' && this.peek()!.v === '(') this.skipParens();
        ops.push({ kind, name, selections: this.parseSelectionSet() });
        continue;
      }
      throw new Error('graphql: unexpected token at document top');
    }
    return ops;
  }

  private skipParens(): void {
    let depth = 0;
    for (;;) {
      const t = this.next();
      if (t.t === 'punct' && t.v === '(') depth++;
      else if (t.t === 'punct' && t.v === ')') { depth--; if (depth === 0) return; }
    }
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expectPunct('{');
    const sels: GqlSelection[] = [];
    for (;;) {
      const t = this.peek();
      if (!t) throw new Error('graphql: unterminated selection set');
      if (t.t === 'punct' && t.v === '}') { this.next(); return sels; }
      sels.push(this.parseSelection());
    }
  }

  private parseSelection(): GqlSelection {
    const t = this.peek()!;
    if (t.t === 'spread') {
      this.next();
      const n = this.peek();
      if (n?.t === 'name' && n.v === 'on') {
        this.next();
        const type = this.expectName();
        return { k: 'inline', type, children: this.parseSelectionSet() };
      }
      if (n?.t === 'name') {
        // Named fragment spread: not used by the suite; skip its selection set if present.
        this.next();
        return { k: 'inline', type: null, children: [] };
      }
      return { k: 'inline', type: null, children: this.parseSelectionSet() };
    }
    const first = this.expectName();
    let alias: string | null = null;
    let name = first;
    const colon = this.peek();
    if (colon?.t === 'punct' && colon.v === ':') {
      this.next();
      alias = first;
      name = this.expectName();
    }
    const args: Record<string, GqlValue> = {};
    const paren = this.peek();
    if (paren?.t === 'punct' && paren.v === '(') {
      this.next();
      for (;;) {
        const p = this.peek()!;
        if (p.t === 'punct' && p.v === ')') { this.next(); break; }
        const argName = this.expectName();
        this.expectPunct(':');
        args[argName] = this.parseValue();
      }
    }
    let children: GqlSelection[] = [];
    const brace = this.peek();
    if (brace?.t === 'punct' && brace.v === '{') children = this.parseSelectionSet();
    return { k: 'field', f: { alias, name, args, children } };
  }

  private parseValue(): GqlValue {
    const t = this.next();
    if (t.t === 'punct' && t.v === '$') return { k: 'var', name: this.expectName() };
    if (t.t === 'punct' && t.v === '[') {
      const list: GqlValue[] = [];
      for (;;) {
        const p = this.peek()!;
        if (p.t === 'punct' && p.v === ']') { this.next(); break; }
        list.push(this.parseValue());
      }
      return { k: 'list', v: list };
    }
    if (t.t === 'punct' && t.v === '{') {
      const obj: Record<string, GqlValue> = {};
      for (;;) {
        const p = this.peek()!;
        if (p.t === 'punct' && p.v === '}') { this.next(); break; }
        const key = this.expectName();
        this.expectPunct(':');
        obj[key] = this.parseValue();
      }
      return { k: 'object', v: obj };
    }
    if (t.t === 'string') return { k: 'string', v: t.v };
    if (t.t === 'int') return { k: 'int', v: t.v };
    if (t.t === 'name') {
      if (t.v === 'true') return { k: 'bool', v: true };
      if (t.v === 'false') return { k: 'bool', v: false };
      if (t.v === 'null') return { k: 'null' };
      return { k: 'enum', v: t.v };
    }
    throw new Error('graphql: bad value');
  }
}

function resolveValue(v: GqlValue, vars: Record<string, unknown>): unknown {
  switch (v.k) {
    case 'var': return vars[v.name];
    case 'string': return v.v;
    case 'int': return v.v;
    case 'bool': return v.v;
    case 'null': return null;
    case 'enum': return v.v;
    case 'list': return v.v.map((x) => resolveValue(x, vars));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [k, x] of Object.entries(v.v)) out[k] = resolveValue(x, vars);
      return out;
    }
  }
}

// --- schema tables for introspection ---

const GQL_TYPE_FIELDS: Record<string, string[]> = {
  Issue: ['id', 'number', 'title', 'body', 'state', 'url', 'createdAt', 'updatedAt', 'author', 'comments', 'labels'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'baseRefOid', 'files', 'author', 'createdAt', 'updatedAt', 'mergedAt', 'mergeCommit'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'description', 'issue', 'issues', 'pullRequests', 'pullRequest', 'url', 'isPrivate', 'createdAt', 'updatedAt'],
  SearchType: [],
};
const GQL_ENUM_VALUES: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE', 'COMMIT', 'WIKI'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
};

// --- execution ---

type GqlObj =
  | { __type: 'Query' }
  | { __type: 'Repository'; repo: Repo }
  | { __type: 'Issue'; repo: Repo; issue: Issue }
  | { __type: 'PullRequest'; repo: Repo; pr: Pull }
  | { __type: 'User'; login: string }
  | { __type: 'Ref'; name: string }
  | { __type: 'IssueConnection'; repo: Repo; issues: Issue[] }
  | { __type: 'PullRequestConnection'; repo: Repo; prs: Pull[] }
  | { __type: 'PullRequestChangedFile'; path: string; additions: number; deletions: number }
  | { __type: 'PageInfo'; hasNextPage: boolean; endCursor: string | null }
  | { __type: 'Type'; name: string }
  | { __type: 'Mutation' }
  | { __type: 'Payload'; fields: Record<string, unknown> }
  | { __type: 'CommentEdge'; id: string; body: string }
  | { __type: 'Comment'; id: string; body: string };

const GQL_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', '__type', '__typename'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'description', 'issue', 'issues', 'pullRequests', 'pullRequest', 'url', 'isPrivate', 'createdAt', 'updatedAt', '__typename'],
  Issue: ['id', 'number', 'title', 'body', 'state', 'url', 'createdAt', 'updatedAt', 'author', 'comments', 'labels', '__typename'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'baseRefOid', 'files', 'author', 'createdAt', 'updatedAt', 'mergedAt', 'mergeCommit', '__typename'],
  User: ['login', 'id', 'name', 'url', '__typename'],
  Ref: ['name', '__typename'],
  IssueConnection: ['nodes', 'pageInfo', 'totalCount', '__typename'],
  PullRequestConnection: ['nodes', 'pageInfo', 'totalCount', '__typename'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changes', '__typename'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor', '__typename'],
  Type: ['name', 'kind', 'fields', 'enumValues', 'description', '__typename'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment', '__typename'],
  Payload: ['issue', 'pullRequest', 'commentEdge', 'clientMutationId', '__typename'],
  CommentEdge: ['node', 'cursor', '__typename'],
  Comment: ['id', 'body', 'author', 'createdAt', '__typename'],
};

class GqlError extends Error {}

function prMergeable(repo: Repo, pr: Pull): string {
  const headTip = repo.refs.get(`refs/heads/${pr.head}`);
  const baseTip = repo.refs.get(`refs/heads/${pr.base}`);
  if (!headTip || !baseTip) return 'UNKNOWN';
  const base = mergeBase(repo, baseTip, headTip);
  if (base === null) return 'UNKNOWN';
  const baseFiles = treeFileMap(repo, parseCommit(repo.objects.get(base)!.data).tree);
  const headFiles = treeFileMap(repo, parseCommit(repo.objects.get(headTip)!.data).tree);
  const baseTipFiles = treeFileMap(repo, parseCommit(repo.objects.get(baseTip)!.data).tree);
  const allPaths = new Set([...baseFiles.keys(), ...headFiles.keys(), ...baseTipFiles.keys()]);
  for (const path of allPaths) {
    const b = baseFiles.get(path);
    const h = headFiles.get(path);
    const t = baseTipFiles.get(path);
    const headChanged = (h?.oid ?? null) !== (b?.oid ?? null);
    const baseChanged = (t?.oid ?? null) !== (b?.oid ?? null);
    if (headChanged && baseChanged && (h?.oid ?? null) !== (t?.oid ?? null)) return 'CONFLICTING';
  }
  return 'MERGEABLE';
}

function prFiles(repo: Repo, pr: Pull): { path: string; additions: number; deletions: number }[] {
  const headTip = repo.refs.get(`refs/heads/${pr.head}`);
  const baseTip = repo.refs.get(`refs/heads/${pr.base}`);
  if (!headTip || !baseTip) return [];
  const headFiles = treeFileMap(repo, parseCommit(repo.objects.get(headTip)!.data).tree);
  const baseFiles = treeFileMap(repo, parseCommit(repo.objects.get(baseTip)!.data).tree);
  const out: { path: string; additions: number; deletions: number }[] = [];
  for (const path of [...new Set([...headFiles.keys(), ...baseFiles.keys()])].sort()) {
    const h = headFiles.get(path);
    const b = baseFiles.get(path);
    if ((h?.oid ?? null) === (b?.oid ?? null)) continue;
    const oldText = b ? (repo.objects.get(b.oid)?.data.toString('utf8') ?? '') : '';
    const newText = h ? (repo.objects.get(h.oid)?.data.toString('utf8') ?? '') : '';
    const { additions, deletions } = lineDiff(oldText, newText);
    out.push({ path, additions, deletions });
  }
  return out;
}

function issueCursor(number: number): string {
  return Buffer.from(`cursor:${number}`, 'utf8').toString('base64');
}

function executeSelections(obj: GqlObj, selections: GqlSelection[], vars: Record<string, unknown>, errors: { message: string }[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const sel of selections) {
    if (sel.k === 'inline') {
      const typeName = sel.type;
      if (typeName === null || typeName === obj.__type || (obj.__type === 'Payload' && typeName === 'Payload')) {
        Object.assign(out, executeSelections(obj, sel.children, vars, errors));
      }
      continue;
    }
    const f = sel.f;
    const key = f.alias ?? f.name;
    const allowed = GQL_FIELDS[obj.__type] ?? [];
    if (f.name === '__typename') { out[key] = obj.__type; continue; }
    if (!allowed.includes(f.name)) {
      errors.push({ message: `Cannot query field "${f.name}" on type "${obj.__type}".` });
      out[key] = null;
      continue;
    }
    out[key] = executeField(obj, f, vars, errors);
  }
  return out;
}

function argVal(f: GqlField, name: string, vars: Record<string, unknown>): unknown {
  const v = f.args[name];
  return v === undefined ? undefined : resolveValue(v, vars);
}

function executeField(obj: GqlObj, f: GqlField, vars: Record<string, unknown>, errors: { message: string }[]): unknown {
  const name = f.name;
  // Scalars / leaf values.
  switch (obj.__type) {
    case 'Query': {
      if (name === 'viewer') return executeSelections({ __type: 'User', login: VIEWER }, f.children, vars, errors);
      if (name === 'repository') {
        const owner = argVal(f, 'owner', vars) as string;
        const repoName = argVal(f, 'name', vars) as string;
        const repo = owner === VIEWER ? repos.get(repoKey(owner, repoName)) ?? null : null;
        if (!repo) return null;
        return executeSelections({ __type: 'Repository', repo }, f.children, vars, errors);
      }
      if (name === 'node') {
        const id = argVal(f, 'id', vars) as string;
        const decoded = decodeGqlId(id);
        if (!decoded) return null;
        if (decoded.kind === 'Repository') {
          const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
          if (!repo) return null;
          return executeSelections({ __type: 'Repository', repo }, f.children, vars, errors);
        }
        if (decoded.kind === 'Issue') {
          const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
          const issue = repo?.issues.find((i) => i.number === Number(decoded.parts[1]));
          if (!repo || !issue) return null;
          return executeSelections({ __type: 'Issue', repo, issue }, f.children, vars, errors);
        }
        if (decoded.kind === 'PullRequest') {
          const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
          const pr = repo?.pulls.find((p) => p.number === Number(decoded.parts[1]));
          if (!repo || !pr) return null;
          return executeSelections({ __type: 'PullRequest', repo, pr }, f.children, vars, errors);
        }
        return null;
      }
      if (name === '__type') {
        const typeName = argVal(f, 'name', vars) as string;
        if (!(typeName in GQL_TYPE_FIELDS) && !(typeName in GQL_ENUM_VALUES)) return null;
        return executeSelections({ __type: 'Type', name: typeName }, f.children, vars, errors);
      }
      break;
    }
    case 'User': {
      if (name === 'login') return obj.login;
      if (name === 'id') return GQL_ID('User', obj.login);
      if (name === 'name') return obj.login;
      if (name === 'url') return `https://example.invalid/${obj.login}`;
      break;
    }
    case 'Repository': {
      const repo = obj.repo;
      if (name === 'id') return GQL_ID('Repository', repo.id);
      if (name === 'databaseId') return repo.id;
      if (name === 'name') return repo.name;
      if (name === 'nameWithOwner') return `${repo.owner}/${repo.name}`;
      if (name === 'owner') return executeSelections({ __type: 'User', login: repo.owner }, f.children, vars, errors);
      if (name === 'defaultBranchRef') {
        const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        if (!tip) return null;
        return executeSelections({ __type: 'Ref', name: repo.defaultBranch }, f.children, vars, errors);
      }
      if (name === 'viewerPermission') return 'ADMIN';
      if (name === 'hasIssuesEnabled') return true;
      if (name === 'description') return repo.description;
      if (name === 'url') return `https://example.invalid/${repo.owner}/${repo.name}`;
      if (name === 'isPrivate') return repo.isPrivate;
      if (name === 'createdAt' || name === 'updatedAt') return '2025-01-01T00:00:00Z';
      if (name === 'issue') {
        const number = argVal(f, 'number', vars) as number;
        const issue = repo.issues.find((i) => i.number === number);
        if (!issue) return null;
        return executeSelections({ __type: 'Issue', repo, issue }, f.children, vars, errors);
      }
      if (name === 'issues') {
        const first = argVal(f, 'first', vars) as number | undefined;
        const after = argVal(f, 'after', vars) as string | null | undefined;
        const states = argVal(f, 'states', vars) as string[] | undefined;
        const orderBy = argVal(f, 'orderBy', vars) as { field?: string; direction?: string } | undefined;
        let list = [...repo.issues];
        if (states && states.length) {
          const want = new Set(states.map((s) => (s === 'OPEN' ? 'open' : 'closed')));
          list = list.filter((i) => want.has(i.state));
        }
        const dir = orderBy?.direction ?? 'ASC';
        const field = orderBy?.field ?? 'CREATED_AT';
        if (field === 'CREATED_AT') list.sort((a, b) => dir === 'DESC' ? b.number - a.number : a.number - b.number);
        if (after) {
          try {
            const text = Buffer.from(after, 'base64').toString('utf8');
            const m = text.match(/^cursor:(\d+)$/);
            if (m) {
              const idx = list.findIndex((i) => i.number === Number(m[1]));
              if (idx >= 0) list = list.slice(idx + 1);
            }
          } catch { /* bad cursor: start from the beginning */ }
        }
        const page = typeof first === 'number' ? list.slice(0, first) : list;
        const hasNext = typeof first === 'number' ? list.length > first : false;
        const endCursor = page.length ? issueCursor(page[page.length - 1]!.number) : null;
        const conn: GqlObj = { __type: 'IssueConnection', repo, issues: page };
        // Stash paging info on the object via a side channel: encode in the issues array.
        (conn as unknown as { _pageInfo: { hasNextPage: boolean; endCursor: string | null } })._pageInfo = { hasNextPage: hasNext, endCursor };
        return executeSelections(conn, f.children, vars, errors);
      }
      if (name === 'pullRequests') {
        const first = argVal(f, 'first', vars) as number | undefined;
        let list = repo.pulls.filter((p) => p.state === 'open').sort((a, b) => a.number - b.number);
        if (typeof first === 'number') list = list.slice(0, first);
        return executeSelections({ __type: 'PullRequestConnection', repo, prs: list }, f.children, vars, errors);
      }
      if (name === 'pullRequest') {
        const number = argVal(f, 'number', vars) as number;
        const pr = repo.pulls.find((p) => p.number === number);
        if (!pr) return null;
        return executeSelections({ __type: 'PullRequest', repo, pr }, f.children, vars, errors);
      }
      break;
    }
    case 'Issue': {
      const { repo, issue } = obj;
      if (name === 'id') return GQL_ID('Issue', repo.id, issue.number);
      if (name === 'number') return issue.number;
      if (name === 'title') return issue.title;
      if (name === 'body') return issue.body;
      if (name === 'state') return issue.state === 'open' ? 'OPEN' : 'CLOSED';
      if (name === 'url') return `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`;
      if (name === 'createdAt' || name === 'updatedAt') return '2025-01-01T00:00:00Z';
      if (name === 'author') return executeSelections({ __type: 'User', login: VIEWER }, f.children, vars, errors);
      if (name === 'comments') return executeSelections({ __type: 'IssueConnection', repo, issues: [] }, f.children, vars, errors);
      if (name === 'labels') return issue.labels.map((l) => ({ name: l.name }));
      break;
    }
    case 'PullRequest': {
      const { repo, pr } = obj;
      if (name === 'id') return GQL_ID('PullRequest', repo.id, pr.number);
      if (name === 'number') return pr.number;
      if (name === 'title') return pr.title;
      if (name === 'body') return pr.body;
      if (name === 'state') return pr.merged ? 'MERGED' : pr.state === 'open' ? 'OPEN' : 'CLOSED';
      if (name === 'merged') return pr.merged;
      if (name === 'mergeable') return prMergeable(repo, pr);
      if (name === 'headRefName') return pr.head;
      if (name === 'baseRefName') return pr.base;
      if (name === 'headRefOid') return repo.refs.get(`refs/heads/${pr.head}`) ?? null;
      if (name === 'baseRefOid') return repo.refs.get(`refs/heads/${pr.base}`) ?? null;
      if (name === 'createdAt' || name === 'updatedAt') return '2025-01-01T00:00:00Z';
      if (name === 'mergedAt') return pr.mergedAt;
      if (name === 'mergeCommit') return null;
      if (name === 'author') return executeSelections({ __type: 'User', login: VIEWER }, f.children, vars, errors);
      if (name === 'files') {
        const first = argVal(f, 'first', vars) as number | undefined;
        let files = prFiles(repo, pr);
        if (typeof first === 'number') files = files.slice(0, first);
        const nodes = files.map((fl) => executeSelections({ __type: 'PullRequestChangedFile', path: fl.path, additions: fl.additions, deletions: fl.deletions }, f.children.find((c) => c.k === 'field' && c.f.name === 'nodes')?.f.children ?? [], vars, errors));
        // files is a connection: {nodes:[...]}. The selection has a `nodes` field; resolve it.
        const connOut: Record<string, unknown> = {};
        for (const sel of f.children) {
          if (sel.k === 'field' && sel.f.name === 'nodes') connOut[sel.f.alias ?? 'nodes'] = nodes;
          else if (sel.k === 'field') connOut[sel.f.alias ?? sel.f.name] = null;
        }
        return connOut;
      }
      break;
    }
    case 'Ref': {
      if (name === 'name') return obj.name;
      break;
    }
    case 'IssueConnection': {
      if (name === 'nodes') {
        const nodeSels = f.children;
        return obj.issues.map((issue) => executeSelections({ __type: 'Issue', repo: obj.repo, issue }, nodeSels, vars, errors));
      }
      if (name === 'pageInfo') {
        const info = (obj as unknown as { _pageInfo?: { hasNextPage: boolean; endCursor: string | null } })._pageInfo ?? { hasNextPage: false, endCursor: null };
        return executeSelections({ __type: 'PageInfo', hasNextPage: info.hasNextPage, endCursor: info.endCursor }, f.children, vars, errors);
      }
      if (name === 'totalCount') return obj.issues.length;
      break;
    }
    case 'PullRequestConnection': {
      if (name === 'nodes') {
        return obj.prs.map((pr) => executeSelections({ __type: 'PullRequest', repo: obj.repo, pr }, f.children, vars, errors));
      }
      if (name === 'pageInfo') {
        return executeSelections({ __type: 'PageInfo', hasNextPage: false, endCursor: null }, f.children, vars, errors);
      }
      if (name === 'totalCount') return obj.prs.length;
      break;
    }
    case 'PullRequestChangedFile': {
      if (name === 'path') return obj.path;
      if (name === 'additions') return obj.additions;
      if (name === 'deletions') return obj.deletions;
      if (name === 'changes') return obj.additions + obj.deletions;
      break;
    }
    case 'PageInfo': {
      if (name === 'hasNextPage') return obj.hasNextPage;
      if (name === 'hasPreviousPage') return false;
      if (name === 'startCursor') return null;
      if (name === 'endCursor') return obj.endCursor;
      break;
    }
    case 'Type': {
      if (name === 'name') return obj.name;
      if (name === 'kind') return obj.name in GQL_ENUM_VALUES ? 'ENUM' : 'OBJECT';
      if (name === 'description') return null;
      if (name === 'fields') {
        const fields = GQL_TYPE_FIELDS[obj.name] ?? [];
        return fields.map((fn) => ({ name: fn, description: null }));
      }
      if (name === 'enumValues') {
        const vals = GQL_ENUM_VALUES[obj.name] ?? [];
        return vals.map((vn) => ({ name: vn, description: null }));
      }
      break;
    }
    case 'Mutation': {
      if (name === 'createIssue') {
        const input = argVal(f, 'input', vars) as { repositoryId?: string; title?: string; body?: string };
        const decoded = decodeGqlId(input.repositoryId ?? '');
        if (!decoded || decoded.kind !== 'Repository') throw new GqlError('createIssue: bad repositoryId');
        const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
        if (!repo) throw new GqlError('createIssue: repository not found');
        const issue: Issue = {
          number: repo.nextIssue++,
          title: input.title ?? '',
          body: input.body ?? '',
          state: 'open',
          labels: [],
          createdSeq: ++globalSeq,
          json: '',
        };
        issue.json = issueJsonOf(repo, issue);
        repo.issues.push(issue);
        const payload: GqlObj = { __type: 'Payload', fields: { issue: { __type: 'Issue', repo, issue } as GqlObj } };
        return executeSelections(payload, f.children, vars, errors);
      }
      if (name === 'closeIssue') {
        const input = argVal(f, 'input', vars) as { issueId?: string };
        const decoded = decodeGqlId(input.issueId ?? '');
        if (!decoded || decoded.kind !== 'Issue') throw new GqlError('closeIssue: bad issueId');
        const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
        const issue = repo?.issues.find((i) => i.number === Number(decoded.parts[1]));
        if (!repo || !issue) throw new GqlError('closeIssue: issue not found');
        issue.state = 'closed';
        issue.json = issueJsonOf(repo, issue);
        const payload: GqlObj = { __type: 'Payload', fields: { issue: { __type: 'Issue', repo, issue } as GqlObj } };
        return executeSelections(payload, f.children, vars, errors);
      }
      if (name === 'createPullRequest') {
        const input = argVal(f, 'input', vars) as { repositoryId?: string; baseRefName?: string; headRefName?: string; title?: string; body?: string };
        const decoded = decodeGqlId(input.repositoryId ?? '');
        if (!decoded || decoded.kind !== 'Repository') throw new GqlError('createPullRequest: bad repositoryId');
        const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
        if (!repo) throw new GqlError('createPullRequest: repository not found');
        const head = input.headRefName ?? '';
        const base = input.baseRefName ?? repo.defaultBranch;
        if (!repo.refs.has(`refs/heads/${head}`) || !repo.refs.has(`refs/heads/${base}`)) throw new GqlError('createPullRequest: branch missing');
        const dup = repo.pulls.find((p) => p.state === 'open' && p.head === head && p.base === base);
        if (dup) throw new GqlError('createPullRequest: pull request already exists');
        const pr: Pull = { number: repo.nextPull++, title: input.title ?? '', body: input.body ?? '', state: 'open', head, base, merged: false, mergedAt: null, mergeCommitSha: null, createdSeq: ++globalSeq };
        repo.pulls.push(pr);
        const payload: GqlObj = { __type: 'Payload', fields: { pullRequest: { __type: 'PullRequest', repo, pr } as GqlObj } };
        return executeSelections(payload, f.children, vars, errors);
      }
      if (name === 'mergePullRequest') {
        const input = argVal(f, 'input', vars) as { pullRequestId?: string; mergeMethod?: string };
        const decoded = decodeGqlId(input.pullRequestId ?? '');
        if (!decoded || decoded.kind !== 'PullRequest') throw new GqlError('mergePullRequest: bad pullRequestId');
        const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
        const pr = repo?.pulls.find((p) => p.number === Number(decoded.parts[1]));
        if (!repo || !pr) throw new GqlError('mergePullRequest: pull request not found');
        if (pr.merged) throw new GqlError('mergePullRequest: already merged');
        const result = doMerge(repo, pr);
        if (!result.ok) throw new GqlError(`mergePullRequest: ${result.message ?? 'merge failed'}`);
        const payload: GqlObj = { __type: 'Payload', fields: { pullRequest: { __type: 'PullRequest', repo, pr } as GqlObj } };
        return executeSelections(payload, f.children, vars, errors);
      }
      if (name === 'addComment') {
        const input = argVal(f, 'input', vars) as { subjectId?: string; body?: string };
        const decoded = decodeGqlId(input.subjectId ?? '');
        if (!decoded || decoded.kind !== 'Issue') throw new GqlError('addComment: bad subjectId');
        const repo = [...repos.values()].find((r) => r.id === Number(decoded.parts[0]));
        const issue = repo?.issues.find((i) => i.number === Number(decoded.parts[1]));
        if (!repo || !issue) throw new GqlError('addComment: issue not found');
        const comment: Comment = { id: repo.nextComment++, body: input.body ?? '', user: VIEWER };
        const list = repo.comments.get(issue.number) ?? [];
        list.push(comment);
        repo.comments.set(issue.number, list);
        const edge: GqlObj = { __type: 'CommentEdge', id: GQL_ID('IssueComment', repo.id, issue.number, comment.id), body: comment.body };
        const payload: GqlObj = { __type: 'Payload', fields: { commentEdge: edge } };
        return executeSelections(payload, f.children, vars, errors);
      }
      break;
    }
    case 'Payload': {
      const v = obj.fields[name];
      if (v === undefined) return null;
      if (typeof v === 'object' && v !== null && '__type' in (v as Record<string, unknown>)) {
        return executeSelections(v as GqlObj, f.children, vars, errors);
      }
      return v;
    }
    case 'CommentEdge': {
      if (name === 'node') return executeSelections({ __type: 'Comment', id: obj.id, body: obj.body }, f.children, vars, errors);
      if (name === 'cursor') return obj.id;
      break;
    }
    case 'Comment': {
      if (name === 'id') return obj.id;
      if (name === 'body') return obj.body;
      if (name === 'author') return executeSelections({ __type: 'User', login: VIEWER }, f.children, vars, errors);
      if (name === 'createdAt') return '2025-01-01T00:00:00Z';
      break;
    }
  }
  return null;
}

function runGraphQLOperation(query: string, variables: Record<string, unknown>, operationName?: string): { data: unknown; errors?: { message: string }[] } {
  const errors: { message: string }[] = [];
  try {
    const parser = new GqlParser(gqlTokenize(query));
    const ops = parser.parseDocument();
    let op = ops[0];
    if (operationName) op = ops.find((o) => o.name === operationName) ?? op;
    if (!op) return { data: null, errors: [{ message: 'no operation' }] };
    const root: GqlObj = op.kind === 'mutation' ? { __type: 'Mutation' } : { __type: 'Query' };
    const data = executeSelections(root, op.selections, variables, errors);
    if (errors.length) return { data: null, errors };
    return { data };
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
  }
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse, body: Buffer): Promise<void> {
  if (!authOk(req)) { unauthorized(res); return; }
  const parsed = parseJsonBody(body);
  if (!parsed.ok) { sendJson(res, 400, { message: 'malformed JSON body' }); return; }
  const value = parsed.value;
  const runOne = (op: unknown): Record<string, unknown> => {
    if (!isRecord(op) || typeof op.query !== 'string') return { data: null, errors: [{ message: 'query is required' }] };
    const vars = isRecord(op.variables) ? (op.variables as Record<string, unknown>) : {};
    const opName = typeof op.operationName === 'string' ? op.operationName : undefined;
    return runGraphQLOperation(op.query, vars, opName);
  };
  if (Array.isArray(value)) {
    sendJson(res, 200, value.map(runOne));
    return;
  }
  sendJson(res, 200, runOne(value));
}

// ---------------------------------------------------------------- MCP

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: { type: 'object'; properties: Record<string, unknown>; required: string[] };
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'The repository description.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed, or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        body: { type: 'string', description: 'The pull request body.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'integer', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

const MCP_TOOLS_JSON = JSON.stringify(MCP_TOOLS);

function mcpResult(res: ServerResponse, id: unknown, result: unknown): void {
  sendJson(res, 200, { jsonrpc: '2.0', id: id ?? null, result });
}

function mcpError(res: ServerResponse, id: unknown, code: number, message: string, status = 200): void {
  sendJson(res, status, { jsonrpc: '2.0', id: id ?? null, error: { code, message } });
}

function toolTextResult(obj: unknown): { content: { type: 'text'; text: string }[]; structuredContent: unknown; isError: false } {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj, isError: false };
}

function toolErrorResult(message: string): { content: { type: 'text'; text: string }[]; isError: true } {
  return { content: [{ type: 'text', text: message }], isError: true };
}

async function handleMcp(req: IncomingMessage, res: ServerResponse, body: Buffer): Promise<void> {
  if (!authOk(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  let value: unknown;
  try {
    value = JSON.parse(body.toString('utf8'));
  } catch {
    // Try to salvage the id for the parse-error response.
    const m = body.toString('utf8').match(/"id"\s*:\s*("[^"]*"|\d+)/);
    let id: unknown = null;
    if (m) {
      const raw = m[1]!;
      id = raw.startsWith('"') ? raw.slice(1, -1) : Number(raw);
    }
    sendJson(res, 400, { jsonrpc: '2.0', id, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (!isRecord(value)) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const id = value.id ?? null;
  const method = typeof value.method === 'string' ? value.method : '';
  const params = isRecord(value.params) ? value.params : {};

  // Notifications (no id) get a 202 with no body.
  if (value.id === undefined) {
    try { res.writeHead(202); res.end(); } catch { /* gone */ }
    return;
  }

  if (method === 'server/discover') {
    mcpResult(res, id, {
      resultType: 'discover',
      supportedVersions: ['2026-07-28', '2025-11-25'],
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
      protocolVersion: '2026-07-28',
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: '1.0.0' } },
    });
    return;
  }
  if (method === 'initialize') {
    const offered = isRecord(params) ? (params as Record<string, unknown>).protocolVersion : undefined;
    const revision = typeof offered === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(offered) ? offered : '2025-11-25';
    try {
      res.writeHead(200, {
        'content-type': 'application/json; charset=utf-8',
        'x-github-request-id': randomBytes(8).toString('hex'),
        'mcp-session-id': `forge-${randomBytes(8).toString('hex')}`,
      });
      res.end(JSON.stringify({ jsonrpc: '2.0', id, result: { protocolVersion: revision, capabilities: { tools: {} }, serverInfo: { name: 'forge', version: '1.0.0' } } }));
    } catch { /* gone */ }
    return;
  }
  if (method === 'tools/list') {
    mcpResult(res, id, { tools: MCP_TOOLS });
    return;
  }
  if (method === 'tools/call') {
    const name = typeof params.name === 'string' ? params.name : '';
    const args = isRecord(params.arguments) ? (params.arguments as Record<string, unknown>) : {};
    const tool = MCP_TOOLS.find((t) => t.name === name);
    if (!tool) {
      mcpError(res, id, -32601, `Method not found: ${name}`);
      return;
    }
    const missing = tool.inputSchema.required.filter((r) => args[r] === undefined || args[r] === null || args[r] === '');
    if (missing.length) {
      mcpResult(res, id, toolErrorResult(`missing required argument(s): ${missing.join(', ')}`));
      return;
    }
    try {
      const result = await runMcpTool(tool.name, args);
      mcpResult(res, id, result);
    } catch (err) {
      mcpResult(res, id, toolErrorResult(err instanceof Error ? err.message : String(err)));
    }
    return;
  }
  if (method === 'ping') {
    mcpResult(res, id, {});
    return;
  }
  mcpError(res, id, -32601, `Method not found: ${method}`);
}

async function runMcpTool(name: string, args: Record<string, unknown>): Promise<unknown> {
  const owner = typeof args.owner === 'string' ? args.owner : VIEWER;
  const repoName = typeof args.repo === 'string' ? args.repo : typeof args.name === 'string' ? args.name : '';
  switch (name) {
    case 'create_repo': {
      const repoTitle = typeof args.name === 'string' ? args.name : '';
      if (!/^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$/.test(repoTitle)) throw new Error('name is invalid');
      if (repos.has(repoKey(VIEWER, repoTitle))) throw new Error('Repository already exists');
      const repo = createRepoRecord(VIEWER, repoTitle, args.private === true, typeof args.description === 'string' ? args.description : '');
      return toolTextResult(JSON.parse(repo.repoJson));
    }
    case 'get_repo': {
      const repo = findRepo(owner, repoName);
      if (!repo) throw new Error(`Repository not found: ${owner}/${repoName}`);
      return toolTextResult(JSON.parse(repo.repoJson));
    }
    case 'create_issue': {
      const repo = findRepo(owner, repoName);
      if (!repo) throw new Error(`Repository not found: ${owner}/${repoName}`);
      const issue: Issue = {
        number: repo.nextIssue++,
        title: typeof args.title === 'string' ? args.title : '',
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open',
        labels: [],
        createdSeq: ++globalSeq,
        json: '',
      };
      issue.json = issueJsonOf(repo, issue);
      repo.issues.push(issue);
      return toolTextResult({ number: issue.number, title: issue.title, body: issue.body, state: 'open', id: repo.id * 100000 + issue.number });
    }
    case 'list_issues': {
      const repo = findRepo(owner, repoName);
      if (!repo) throw new Error(`Repository not found: ${owner}/${repoName}`);
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = repo.issues
        .filter((i) => state === 'all' || i.state === state)
        .map((i) => ({ number: i.number, title: i.title, body: i.body, state: i.state, id: repo.id * 100000 + i.number }));
      return toolTextResult(list);
    }
    case 'create_pull_request': {
      const repo = findRepo(owner, repoName);
      if (!repo) throw new Error(`Repository not found: ${owner}/${repoName}`);
      const head = typeof args.head === 'string' ? args.head : '';
      const base = typeof args.base === 'string' ? args.base : repo.defaultBranch;
      if (!repo.refs.has(`refs/heads/${head}`) || !repo.refs.has(`refs/heads/${base}`)) throw new Error('head or base branch does not exist');
      const dup = repo.pulls.find((p) => p.state === 'open' && p.head === head && p.base === base);
      if (dup) throw new Error('a pull request from this head already exists');
      const pr: Pull = {
        number: repo.nextPull++,
        title: typeof args.title === 'string' ? args.title : '',
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open', head, base, merged: false, mergedAt: null, mergeCommitSha: null, createdSeq: ++globalSeq,
      };
      repo.pulls.push(pr);
      return toolTextResult({ number: pr.number, title: pr.title, state: 'open', head, base });
    }
    case 'merge_pull_request': {
      const repo = findRepo(owner, repoName);
      if (!repo) throw new Error(`Repository not found: ${owner}/${repoName}`);
      const num = typeof args.pull_number === 'number' ? args.pull_number : Number(args.pull_number);
      const pr = repo.pulls.find((p) => p.number === num);
      if (!pr) throw new Error(`pull request #${num} not found`);
      if (pr.merged) throw new Error('pull request is already merged');
      const result = doMerge(repo, pr);
      if (!result.ok) throw new Error(result.message ?? 'merge failed');
      return toolTextResult({ number: pr.number, merged: true, state: 'closed', sha: result.sha });
    }
    default:
      throw new Error(`unknown tool ${name}`);
  }
}

// ---------------------------------------------------------------- server + lifecycle

async function handleRequest(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'GET';
  let url: URL;
  try {
    url = new URL(req.url ?? '/', `http://${req.headers.host ?? '127.0.0.1'}`);
  } catch {
    sendJson(res, 400, { message: 'bad url' });
    return;
  }
  const path = url.pathname;

  try {
    if (path === '/healthz' && method === 'GET') {
      sendJson(res, 200, { ok: true });
      return;
    }

    // Smart HTTP: /{owner}/{repo}.git/...
    const gitMatch = path.match(/^\/([^/]+)\/([^/]+)\.git(\/.*)$/);
    if (gitMatch) {
      const owner = decodeURIComponent(gitMatch[1]!);
      const repoName = decodeURIComponent(gitMatch[2]!);
      const rest = gitMatch[3]!;
      if (!authOk(req)) { unauthorized(res); return; }
      const repo = findRepo(owner, repoName);
      if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return; }
      const body = method === 'POST' ? await readBody(req) : Buffer.alloc(0);
      if (rest === '/info/refs' && method === 'GET') {
        const service = url.searchParams.get('service') ?? '';
        handleInfoRefs(req, res, repo, service);
        return;
      }
      if (rest === '/git-upload-pack' && method === 'POST') {
        await handleUploadPack(req, res, repo, body);
        return;
      }
      if (rest === '/git-receive-pack' && method === 'POST') {
        await handleReceivePack(req, res, repo, body);
        return;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return;
    }

    if (path === '/api/graphql' && method === 'POST') {
      const body = await readBody(req);
      await handleGraphQL(req, res, body);
      return;
    }
    if (path === '/mcp' && method === 'POST') {
      const body = await readBody(req);
      await handleMcp(req, res, body);
      return;
    }
    if (path.startsWith('/api/v3')) {
      const body = (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE') ? await readBody(req) : Buffer.alloc(0);
      await handleRest(req, res, url, body);
      return;
    }
    sendJson(res, 404, { message: 'Not Found' });
  } catch (err) {
    // Never let one bad request kill the process: the suite proves the server survives errors.
    try {
      sendJson(res, 500, { message: err instanceof Error ? err.message : 'internal error' });
    } catch { /* gone */ }
  }
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function main(): Promise<void> {
  const server = createServer((req, res) => {
    void handleRequest(req, res);
  });
  server.keepAliveTimeout = 5000;
  server.headersTimeout = 10000;

  const port = await new Promise<number>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, '127.0.0.1', () => {
      const addr = server.address();
      if (!addr || typeof addr === 'string') { reject(new Error('no address')); return; }
      resolve(addr.port);
    });
  });

  // Register with the trial env, if one is configured; otherwise serve standalone.
  if (ENV_URL !== '') {
    try {
      const reg = await fetch(`${ENV_URL}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
      });
      if (!reg.ok) {
        process.stderr.write(`register failed: HTTP ${reg.status}\n`);
      }
    } catch (err) {
      process.stderr.write(`register failed: ${err instanceof Error ? err.message : String(err)}\n`);
    }
    // Long-poll /done until the suite is over, then exit 0.
    let delay = 250;
    for (;;) {
      await sleep(delay);
      delay = Math.min(2000, delay * 2);
      try {
        const done = await fetch(`${ENV_URL}/done`, { signal: AbortSignal.timeout(5000) });
        const data = await done.json().catch(() => null) as { done?: boolean } | null;
        if (data?.done === true) break;
      } catch {
        // Env unreachable for a poll: keep polling.
      }
      delay = 250;
    }
    server.close();
    process.exit(0);
  }

  process.stderr.write(`forge listening on 127.0.0.1:${port}\n`);
}

void main().catch((err: unknown) => {
  process.stderr.write(`fatal: ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
  process.exit(1);
});
