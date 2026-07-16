import assert from 'node:assert/strict'
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import {
  compileSite,
  renderSiteModel,
  resolveTourContent,
  rewriteMarkdownLinks,
  validateJsonSchema,
} from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const fixture = join(siteDir, 'fixtures', 'page-manifest', 'valid.json')

const validManifest = JSON.parse(readFileSync(fixture, 'utf8'))
const temp = mkdtempSync(join(tmpdir(), 'bang-site-model-'))
let caseCount = 0
let schemaCaseCount = 0

function compileMutation(name, mutate) {
  const manifest = structuredClone(validManifest)
  mutate(manifest)
  const manifestPath = join(temp, `${name}.json`)
  writeFileSync(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`)
  return compileSite({ manifestPath, repoRoot })
}

function expectReject(name, mutate, pattern) {
  assert.throws(() => compileMutation(name, mutate), pattern)
  caseCount += 1
}

function writeSchemaRegistry(name, schemas) {
  const schemaDir = join(temp, name)
  mkdirSync(schemaDir)
  for (const [filename, schema] of Object.entries(schemas)) {
    writeFileSync(join(schemaDir, filename), `${JSON.stringify(schema, null, 2)}\n`)
  }
  return join(schemaDir, 'example.schema.json')
}

const site = compileSite({ manifestPath: fixture, repoRoot })
assert.deepEqual(site.sections.map((section) => section.id), [
  'start',
  'learn',
  'reference',
  'contribute',
  'architecture',
  'project',
])
assert.deepEqual(site.sidebar[0], {
  text: 'Start',
  items: [{ text: 'What BANG is', link: '/' }],
})
assert.equal(site.pages.length, 1)
assert.deepEqual(site.routeChoices, [
  {
    id: 'language',
    title: 'Frontend / language',
    summary: 'Change parsing, surface syntax, or type checking.',
    order: 10,
    targetPage: 'what-bang-is',
    target: '/',
    seams: ['README.md'],
    firstChange: 'Adjust one checked surface fixture.',
    narrowGate: 'just check Bang/Frontend/TypeCheck.lean',
    fullGate: 'just verify',
  },
])
const onboardingGenerated = compileMutation('onboarding-generated-page', (manifest) => {
  manifest.pages.push({
    id: 'contributor-routes',
    title: 'Choose a contributor route',
    section: 'contribute',
    audience: ['contributor', 'agent'],
    lifecycle: 'snapshot',
    prerequisites: ['what-bang-is'],
    status: { kind: 'not-applicable', reason: 'generated-onboarding' },
    target: {
      kind: 'onboarding-page',
      route: '/contribute/routes',
      contentKey: 'contributor-routes',
    },
    navigation: { order: 10 },
  })
})
assert.equal(
  onboardingGenerated.routeToPage.get('/contribute/routes').source,
  '@onboarding-page:contributor-routes',
)
assert.equal(
  rewriteMarkdownLinks({
    line: '[ftp](ftp://example.com/spec.md)', site, repoRoot, sourcePath: 'README.md',
  }),
  '[ftp](ftp://example.com/spec.md)',
)
assert.equal(
  rewriteMarkdownLinks({
    line: '[cdn](//example.com/spec.md)', site, repoRoot, sourcePath: 'README.md',
  }),
  '[cdn](//example.com/spec.md)',
)
const vocsConfig = readFileSync(join(siteDir, 'vocs.config.ts'), 'utf8')
assert.match(vocsConfig, /sidebar:\s*site\.sidebar/)
assert.doesNotMatch(vocsConfig, /sidebar:\s*\[/)
const synchronizer = readFileSync(join(siteDir, 'sync-docs.mjs'), 'utf8')
assert.doesNotMatch(synchronizer, /const\s+(?:rootFiles|dirs)\s*=/)
const onboardingSource = readFileSync(join(repoRoot, 'ONBOARDING.md'), 'utf8')
assert.match(onboardingSource, /https:\/\/phibkro\.github\.io\/bang\/learn\/common-journey-evidence/)
assert.match(onboardingSource, /https:\/\/phibkro\.github\.io\/bang\/contribute\/routes/)
assert.doesNotMatch(onboardingSource, /\]\(\/(?:learn\/common-journey-evidence|contribute\/routes)\)/)
const tourContent = readFileSync(join(siteDir, 'tour-content.mjs'), 'utf8')
assert.doesNotMatch(tourContent, /^\s*(?:n|slug|title):/m)
assert.equal(
  renderSiteModel(site),
  renderSiteModel(compileSite({ manifestPath: fixture, repoRoot })),
)

try {
  const commonSchema = {
    $schema: 'https://json-schema.org/draft/2020-12/schema',
    $id: 'https://example.test/schema/common.schema.json',
    $defs: { sharedText: { type: 'string', minLength: 1 } },
  }
  const exampleSchema = {
    $schema: 'https://json-schema.org/draft/2020-12/schema',
    $id: 'https://example.test/schema/example.schema.json',
    type: 'object',
    required: ['name'],
    properties: { name: { $ref: 'common.schema.json#/$defs/sharedText' } },
  }
  const schemaCases = [
    {
      name: 'valid-external-reference',
      schemas: {
        'common.schema.json': commonSchema,
        'example.schema.json': exampleSchema,
      },
      data: { name: 'valid' },
    },
    {
      name: 'missing-external-schema',
      schemas: { 'example.schema.json': exampleSchema },
      data: { name: 'valid' },
      reject: /schema validation failed/,
    },
    {
      name: 'incompatible-schema-id',
      schemas: {
        'common.schema.json': {
          ...commonSchema,
          $id: 'https://other.test/schema/common.schema.json',
        },
        'example.schema.json': exampleSchema,
      },
      data: { name: 'valid' },
      reject: /schema validation failed/,
    },
    {
      name: 'missing-schema-id',
      schemas: {
        'common.schema.json': { ...commonSchema, $id: undefined },
        'example.schema.json': exampleSchema,
      },
      data: { name: 'valid' },
      reject: /schema validation failed/,
    },
    {
      name: 'duplicate-schema-id',
      schemas: {
        'common.schema.json': { ...commonSchema, $id: exampleSchema.$id },
        'example.schema.json': exampleSchema,
      },
      data: { name: 'valid' },
      reject: /schema validation failed/,
    },
    {
      name: 'invalid-sibling-schema',
      schemas: {
        'common.schema.json': { ...commonSchema, type: 7 },
        'example.schema.json': exampleSchema,
      },
      data: { name: 'valid' },
      reject: /schema validation failed/,
    },
    {
      name: 'shared-definition-rejects-data',
      schemas: {
        'common.schema.json': commonSchema,
        'example.schema.json': exampleSchema,
      },
      data: { name: '' },
      reject: /schema validation failed/,
    },
  ]
  const adapter = process.env.BANG_SITE_SCHEMA_ADAPTER === 'python' ? 'python' : 'ajv'
  for (const schemaCase of schemaCases) {
    const selectedPath = writeSchemaRegistry(`${adapter}-${schemaCase.name}`, schemaCase.schemas)
    const validate = () => validateJsonSchema({
      data: schemaCase.data,
      schemaPath: selectedPath,
      label: `schema registry ${schemaCase.name}`,
    })
    if (schemaCase.reject) assert.throws(validate, schemaCase.reject)
    else assert.doesNotThrow(validate)
    schemaCaseCount += 1
  }

  const evidenced = compileMutation('evidence-status', (manifest) => {
    manifest.pages[0].status = {
      kind: 'evidence',
      fact: 'docfacts/examples/logger-counting.json',
      schema: 'docfacts/schema/example.schema.json',
      pointer: '/evidence/0',
    }
  })
  assert.equal(evidenced.pages[0].status.label, 'differential-tested')
  assert.match(evidenced.sidebar[0].items[0].text, /Differential-tested/)

  const invalidProductionFact = JSON.parse(
    readFileSync(join(repoRoot, 'docfacts', 'examples', 'logger-counting.json'), 'utf8'),
  )
  invalidProductionFact.summary = ''
  assert.throws(
    () => validateJsonSchema({
      data: invalidProductionFact,
      schemaPath: join(repoRoot, 'docfacts', 'schema', 'example.schema.json'),
      label: 'production example fact using common schema',
    }),
    /schema validation failed/,
  )
  schemaCaseCount += 1

  expectReject('invalid-evidence-pointer', (broken) => {
    broken.pages[0].status = {
      kind: 'evidence',
      fact: 'docfacts/examples/logger-counting.json',
      schema: 'docfacts/schema/example.schema.json',
      pointer: '/evidence/99',
    }
  }, /evidence pointer does not resolve.*\/evidence\/99/)

  const tourSite = compileMutation('tour-page', (manifest) => {
    manifest.pages.push({
      id: 'tour-fixture',
      title: 'Tour fixture',
      section: 'learn',
      audience: ['consumer'],
      lifecycle: 'snapshot',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'generated-lesson' },
      target: { kind: 'tour-lesson', route: '/tour-fixture', contentKey: 'tour-fixture' },
      navigation: { order: 10 },
    })
  })
  assert.throws(
    () => resolveTourContent(tourSite, []),
    /manifest lesson 'tour-fixture' has no tour content/,
  )
  caseCount += 1
  assert.throws(
    () => resolveTourContent(tourSite, [{
      key: 'tour-fixture',
      teaches: 'fixture',
      seeds: [],
      prose: 'fixture',
      title: 'content must not own title',
    }]),
    /fields are owned by the page manifest: title/,
  )
  caseCount += 1
  const duplicateTourKey = compileMutation('duplicate-tour-key', (manifest) => {
    const base = {
      title: 'Tour fixture',
      section: 'learn',
      audience: ['consumer'],
      lifecycle: 'snapshot',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'generated-lesson' },
    }
    manifest.pages.push({
      ...base,
      id: 'tour-fixture-one',
      target: { kind: 'tour-lesson', route: '/tour-fixture-one', contentKey: 'same-key' },
      navigation: { order: 10 },
    })
    manifest.pages.push({
      ...base,
      id: 'tour-fixture-two',
      target: { kind: 'tour-lesson', route: '/tour-fixture-two', contentKey: 'same-key' },
      navigation: { order: 20 },
    })
  })
  assert.throws(
    () => resolveTourContent(duplicateTourKey, [{
      key: 'same-key', teaches: 'fixture', seeds: [], prose: 'fixture',
    }]),
    /duplicate tour content key same-key/,
  )
  caseCount += 1

  const catalog = compileMutation('catalog-publication', (manifest) => {
    manifest.publications.push({
      kind: 'tree',
      mode: 'catalog',
      sourceRoot: 'docs/reference',
      routePrefix: '/reference',
      defaults: {
        audience: ['consumer', 'contributor', 'agent'],
        lifecycle: 'snapshot',
        status: { kind: 'not-applicable', reason: 'catalog-page' },
      },
    })
  })
  const catalogPage = catalog.emittedPages.find((page) =>
    page.source === 'docs/reference/language.md' && page.route === '/reference/language')
  assert.deepEqual(catalogPage.audience, ['consumer', 'contributor', 'agent'])
  assert.equal(catalogPage.lifecycle, 'snapshot')
  assert.equal(catalogPage.status.kind, 'not-applicable')

  expectReject('missing-route-choices', (broken) => {
    delete broken.routeChoices
  }, /routeChoices.*required|required.*routeChoices/)

  expectReject('duplicate-route-choice-id', (broken) => {
    broken.routeChoices.push({ ...structuredClone(broken.routeChoices[0]), order: 20 })
  }, /duplicate route choice id.*language/)

  expectReject('duplicate-route-choice-order', (broken) => {
    broken.routeChoices.push({
      ...structuredClone(broken.routeChoices[0]),
      id: 'proof',
      title: 'Kernel / proof',
    })
  }, /duplicate route choice order.*10/)

  expectReject('missing-route-choice-target', (broken) => {
    broken.routeChoices[0].targetPage = 'missing-page'
  }, /route choice language targets missing page missing-page/)

  expectReject('untracked-route-choice-seam', (broken) => {
    broken.routeChoices[0].seams = ['missing/seam.lean']
  }, /tracked source does not exist.*missing\/seam\.lean/)

  expectReject('volatile-route-choice-target', (broken) => {
    broken.pages.push({
      id: 'current-context',
      title: 'Current context',
      section: 'project',
      audience: ['contributor', 'agent'],
      lifecycle: 'now',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'repository-state' },
      target: { kind: 'repository-link', path: 'CONTEXT.md', view: 'blob' },
      navigation: false,
    })
    broken.routeChoices[0].targetPage = 'current-context'
  }, /route choice language targets volatile page current-context/)

  expectReject('missing-route-choice-gate', (broken) => {
    broken.routeChoices[0].narrowGate = ''
  }, /schema validation failed/)

  expectReject('missing-audience', (broken) => {
    delete broken.pages[0].audience
  }, /audience.*required|required.*audience/)

  expectReject('untracked-source', (broken) => {
    broken.publications[0].source = 'web/docs/fixtures/page-manifest/not-tracked.md'
    broken.pages[0].target.path = broken.publications[0].source
  }, /tracked source.*not-tracked\.md/)

  expectReject('unmanaged-exact-source', (broken) => {
    broken.publications.push({
      kind: 'exact',
      mode: 'managed',
      source: 'ONBOARDING.md',
      route: '/ONBOARDING',
    })
    broken.pages[0].target = {
      kind: 'markdown',
      path: 'ONBOARDING.md',
      route: '/ONBOARDING',
    }
  }, /managed publication.*README\.md/)

  expectReject('duplicate-route', (broken) => {
    broken.pages.push({
      ...structuredClone(broken.pages[0]),
      id: 'duplicate-home',
      navigation: { order: 20 },
    })
  }, /duplicate route.*\//)

  expectReject('duplicate-publication-source', (broken) => {
    broken.publications.push({
      kind: 'exact',
      mode: 'managed',
      source: 'README.md',
      route: '/home-copy',
    })
    broken.pages.push({
      ...structuredClone(broken.pages[0]),
      id: 'home-copy',
      section: 'reference',
      target: { kind: 'markdown', path: 'README.md', route: '/home-copy' },
      navigation: { order: 10 },
    })
  }, /duplicate publication source README\.md/)

  expectReject('case-folded-route', (broken) => {
    const base = {
      title: 'Tour case',
      section: 'reference',
      audience: ['consumer'],
      lifecycle: 'snapshot',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'generated-index' },
    }
    broken.pages.push({
      ...base,
      id: 'upper-tour',
      target: { kind: 'tour-index', route: '/Tour' },
      navigation: { order: 10 },
    })
    broken.pages.push({
      ...base,
      id: 'lower-tour',
      target: { kind: 'tour-index', route: '/tour' },
      navigation: { order: 20 },
    })
  }, /duplicate emitted route.*\/tour/i)

  expectReject('dangling-prerequisite', (broken) => {
    broken.pages[0].prerequisites = ['missing-page']
  }, /prerequisite missing-page.*does not exist/)

  expectReject('prerequisite-cycle', (broken) => {
    broken.pages[0].prerequisites = ['cycle-page']
    broken.pages.push({
      id: 'cycle-page',
      title: 'Cycle page',
      section: 'reference',
      audience: ['consumer'],
      lifecycle: 'snapshot',
      prerequisites: ['what-bang-is'],
      status: { kind: 'not-applicable', reason: 'generated-index' },
      target: { kind: 'tour-index', route: '/cycle-page' },
      navigation: { order: 10 },
    })
  }, /prerequisite cycle/)

  expectReject('local-now-page', (broken) => {
    broken.pages[0].lifecycle = 'now'
  }, /lifecycle now.*repository-link/)

  expectReject('volatile-publication', (broken) => {
    broken.publications[0].source = 'CONTEXT.md'
    broken.publications[0].route = '/CONTEXT'
    broken.pages[0].target.path = 'CONTEXT.md'
    broken.pages[0].target.route = '/CONTEXT'
  }, /public boundary forbids source.*CONTEXT\.md/)

  expectReject('dot-segment-source', (broken) => {
    broken.publications[0].source = './README.md'
    broken.pages[0].target.path = './README.md'
  }, /schema validation failed/)

  expectReject('hidden-tour-lesson', (broken) => {
    broken.pages.push({
      id: 'hidden-tour',
      title: 'Hidden tour',
      section: 'learn',
      audience: ['consumer'],
      lifecycle: 'snapshot',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'generated-lesson' },
      target: { kind: 'tour-lesson', route: '/hidden-tour', contentKey: 'hidden-tour' },
      navigation: false,
    })
  }, /tour lesson must be navigable.*hidden-tour/)

  expectReject('base-path-prefixed-route', (broken) => {
    broken.publications[0].route = '/bang/home'
    broken.pages[0].target.route = '/bang/home'
  }, /route must be base-path-free.*\/bang\/home/)

  expectReject('missing-repository-link', (broken) => {
    broken.pages.push({
      id: 'missing-repository-state',
      title: 'Missing repository state',
      section: 'project',
      audience: ['contributor', 'agent'],
      lifecycle: 'now',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'repository-state' },
      target: {
        kind: 'repository-link',
        path: 'missing-current-state.md',
        view: 'blob',
      },
      navigation: { order: 10 },
    })
  }, /repository-link target does not exist.*missing-current-state\.md/)

  expectReject('competing-frontmatter', (broken) => {
    broken.publications.push({
      kind: 'tree',
      mode: 'catalog',
      sourceRoot: 'docs/notes',
      routePrefix: '/notes',
      defaults: {
        audience: ['contributor', 'agent'],
        lifecycle: 'snapshot',
        status: { kind: 'not-applicable', reason: 'catalog-page' },
      },
    })
    broken.pages.push({
      id: 'wasmfx-target-drift',
      title: 'WasmFX target drift',
      section: 'reference',
      audience: ['contributor', 'agent'],
      lifecycle: 'snapshot',
      prerequisites: [],
      status: { kind: 'not-applicable', reason: 'navigation-only' },
      target: {
        kind: 'markdown',
        path: 'docs/notes/questions/Q9-wasmfx-target-drift.md',
        route: '/notes/questions/Q9-wasmfx-target-drift',
      },
      navigation: { order: 10 },
    })
  }, /frontmatter key status.*owned by the page manifest/)
} finally {
  rmSync(temp, { recursive: true, force: true })
}

console.log(
  `site-model: PASS — valid navigation + ${caseCount}/${caseCount} rejection poles + ` +
  `${schemaCaseCount}/${schemaCaseCount} schema registry adapter cases`,
)
