import assert from 'node:assert/strict'
import { isAbsolute, join, resolve } from 'node:path'

function validateRoleLabLane({ lane, repoRoot, base, run }) {
  assert.ok(isAbsolute(lane), 'BANG_ROLE_LAB_LANE is an absolute path')
  assert.notEqual(resolve(lane), resolve(repoRoot), 'shared role-lab lane is distinct from the source checkout')
  assert.equal(
    resolve(run('git', ['rev-parse', '--show-toplevel'], { cwd: lane }).trim()),
    resolve(lane),
    'shared role-lab path is its checkout root',
  )
  assert.equal(
    run('git', ['rev-parse', 'HEAD'], { cwd: lane }).trim(),
    base,
    'role-lab lane is exact source HEAD',
  )
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'exact-HEAD lane starts clean')
}

export function acquireRoleLabLane({
  repoRoot,
  parent,
  base,
  labKey,
  run,
  env = process.env,
}) {
  const handedOffLane = env.BANG_ROLE_LAB_LANE
  const shared = handedOffLane !== undefined && handedOffLane !== ''
  const lane = shared ? handedOffLane : join(parent, 'repo')

  if (shared) {
    assert.equal(
      env.BANG_ROLE_LAB_HEAD,
      base,
      'BANG_ROLE_LAB_HEAD names the harness source HEAD',
    )
  } else {
    const branch = `practice/${labKey}-harness-${process.pid}-${Date.now()}`
    run(join(repoRoot, 'tools', 'new-worktree.sh'), [lane, branch, base])
  }

  validateRoleLabLane({ lane, repoRoot, base, run })
  return { lane, shared }
}
