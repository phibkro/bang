import assert from 'node:assert/strict'
import { acquireRoleLabLane } from './role-lab-lane.mjs'

const repoRoot = '/repo/source'
const parent = '/tmp/role-lab-test'
const base = '0123456789abcdef'

function fakeRun({ topLevel = '/tmp/shared-lane', head = base, status = '' } = {}) {
  const calls = []
  const run = (command, args, { cwd = repoRoot } = {}) => {
    calls.push({ command, args, cwd })
    if (command.endsWith('/tools/new-worktree.sh')) return ''
    if (command === 'git' && args.join(' ') === 'rev-parse --show-toplevel') return `${topLevel}\n`
    if (command === 'git' && args.join(' ') === 'rev-parse HEAD') return `${head}\n`
    if (command === 'git' && args.join(' ') === 'status --porcelain') return status
    assert.fail(`unexpected command: ${command} ${args.join(' ')}`)
  }
  return { calls, run }
}

{
  const lane = `${parent}/repo`
  const fake = fakeRun({ topLevel: lane })
  const acquired = acquireRoleLabLane({
    repoRoot,
    parent,
    base,
    labKey: 'kernel-proof',
    run: fake.run,
    env: {},
  })
  assert.deepEqual(acquired, { lane, shared: false })
  assert.equal(
    fake.calls.filter(({ command }) => command.endsWith('/tools/new-worktree.sh')).length,
    1,
    'standalone harness creates exactly one private exact-HEAD lane',
  )
}

{
  const lane = '/tmp/shared-lane'
  const fake = fakeRun()
  const acquired = acquireRoleLabLane({
    repoRoot,
    parent,
    base,
    labKey: 'machine-backend',
    run: fake.run,
    env: { BANG_ROLE_LAB_LANE: lane, BANG_ROLE_LAB_HEAD: base },
  })
  assert.deepEqual(acquired, { lane, shared: true })
  assert.equal(
    fake.calls.filter(({ command }) => command.endsWith('/tools/new-worktree.sh')).length,
    0,
    'handoff consumes the runner-owned lane without cloning',
  )
}

for (const [name, env, options, pattern] of [
  ['missing head handoff', { BANG_ROLE_LAB_LANE: '/tmp/shared-lane' }, {}, /BANG_ROLE_LAB_HEAD/],
  ['wrong handoff head', { BANG_ROLE_LAB_LANE: '/tmp/shared-lane', BANG_ROLE_LAB_HEAD: 'wrong' }, {}, /source HEAD/],
  ['relative lane', { BANG_ROLE_LAB_LANE: 'shared-lane', BANG_ROLE_LAB_HEAD: base }, {}, /absolute/],
  ['source checkout reused', { BANG_ROLE_LAB_LANE: repoRoot, BANG_ROLE_LAB_HEAD: base }, { topLevel: repoRoot }, /distinct/],
  ['wrong checkout root', { BANG_ROLE_LAB_LANE: '/tmp/shared-lane', BANG_ROLE_LAB_HEAD: base }, { topLevel: '/tmp/other' }, /checkout root/],
  ['wrong lane head', { BANG_ROLE_LAB_LANE: '/tmp/shared-lane', BANG_ROLE_LAB_HEAD: base }, { head: 'wrong' }, /exact source HEAD/],
  ['dirty lane', { BANG_ROLE_LAB_LANE: '/tmp/shared-lane', BANG_ROLE_LAB_HEAD: base }, { status: '?? fixture\n' }, /starts clean/],
]) {
  const fake = fakeRun(options)
  assert.throws(
    () => acquireRoleLabLane({ repoRoot, parent, base, labKey: name, run: fake.run, env }),
    pattern,
    name,
  )
}

console.log('role-lab-lane: PASS — standalone ownership + 7 shared-lane falsifier poles')
