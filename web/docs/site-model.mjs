import { execFileSync, spawnSync } from 'node:child_process'
import { readFileSync, readdirSync } from 'node:fs'
import { createRequire } from 'node:module'
import { basename, dirname, join, posix } from 'node:path'
import { fileURLToPath } from 'node:url'

const siteDir = dirname(fileURLToPath(import.meta.url))
const require = createRequire(import.meta.url)
const schemaPath = join(siteDir, 'page-manifest.schema.json')
const requiredSections = [
  'start',
  'learn',
  'reference',
  'contribute',
  'architecture',
  'project',
]

function loadJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'))
}

function loadSchemaRegistry(selectedPath) {
  const schemaDir = dirname(selectedPath)
  const schemas = readdirSync(schemaDir)
    .filter((name) => name.endsWith('.schema.json'))
    .sort()
    .map((name) => {
      const path = join(schemaDir, name)
      return { path, schema: loadJson(path) }
    })
  const ids = new Map()
  for (const { path, schema } of schemas) {
    if (typeof schema.$id !== 'string' || schema.$id.length === 0) {
      throw new Error(`schema ${basename(path)} has no $id`)
    }
    try {
      new URL(schema.$id)
    } catch {
      throw new Error(`schema ${basename(path)} has an incompatible $id: ${schema.$id}`)
    }
    if (ids.has(schema.$id)) {
      throw new Error(`duplicate schema $id ${schema.$id}: ${ids.get(schema.$id)} and ${basename(path)}`)
    }
    ids.set(schema.$id, basename(path))
  }
  const selected = schemas.find(({ path }) => path === selectedPath)
  if (!selected) throw new Error(`selected schema is not registered: ${basename(selectedPath)}`)
  return { schemas, selected }
}

export function validateJsonSchema({ data, schemaPath: selectedPath, label }) {
  try {
    const { schemas, selected } = loadSchemaRegistry(selectedPath)
    if (process.env.BANG_SITE_SCHEMA_ADAPTER !== 'python') {
      const Ajv2020Module = require('ajv/dist/2020.js')
      const Ajv2020 = Ajv2020Module.default ?? Ajv2020Module
      const ajv = new Ajv2020({ allErrors: true, strict: true })
      for (const { schema } of schemas) ajv.addSchema(schema)
      const validate = ajv.getSchema(selected.schema.$id)
      if (validate(data)) return
      const detail = ajv.errorsText(validate.errors, { separator: '\n' })
      throw new Error(detail)
    }

    // Fitness explicitly selects the Python adapter. Production never silently
    // falls back: a missing locked Ajv dependency must fail the site build.
    const script = [
      'import json, sys',
      'from pathlib import Path',
      'from tools.docfacts_common import schema_validator',
      'data = json.load(sys.stdin)',
      'errors = sorted(schema_validator(Path(sys.argv[1])).iter_errors(data), key=lambda e: list(e.path))',
      'print("\\n".join(("/" + "/".join(map(str, e.path)) + ": " + e.message) for e in errors))',
      'sys.exit(1 if errors else 0)',
    ].join('; ')
    const result = spawnSync('python3', ['-c', script, selectedPath], {
      cwd: join(siteDir, '..', '..'),
      input: JSON.stringify(data),
      encoding: 'utf8',
    })
    if (result.error) throw result.error
    if (result.status !== 0) throw new Error((result.stdout || result.stderr).trim())
  } catch (error) {
    throw new Error(`${label} schema validation failed:\n${error.message}`, { cause: error })
  }
}

function validateSchema(manifest) {
  validateJsonSchema({ data: manifest, schemaPath, label: 'page manifest' })
}

function localLink(page, repository) {
  if (page.target.kind !== 'repository-link') return page.target.route
  return `${repository.url}/${page.target.view}/${repository.branch}/${page.target.path}`
}

function trackedSources(repoRoot, source, tree = false) {
  try {
    const args = tree
      ? ['--literal-pathspecs', '-C', repoRoot, 'ls-files', '--', source]
      : ['--literal-pathspecs', '-C', repoRoot, 'ls-files', '--error-unmatch', '--', source]
    const output = execFileSync('git', args, {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    }).trim()
    const files = output.length === 0 ? [] : output.split('\n').sort()
    if (files.length === 0) throw new Error('empty source')
    return files
  } catch {
    throw new Error(`page manifest tracked source does not exist: ${source}`)
  }
}

function requireTrackedSource(repoRoot, source) {
  trackedSources(repoRoot, source, false)
}

function requireRepositoryTarget(repoRoot, target) {
  try {
    trackedSources(repoRoot, target.path, target.view === 'tree')
  } catch {
    throw new Error(`page manifest repository-link target does not exist: ${target.path}`)
  }
}

function requirePublicSource(source) {
  const normalized = posix.normalize(source.replaceAll('\\', '/'))
  const denied = normalized === 'CONTEXT.md' ||
    normalized.startsWith('paths/') ||
    normalized.startsWith('scratch/')
  if (denied) throw new Error(`page manifest public boundary forbids source: ${source}`)
}

function rejectManifestFrontmatter(repoRoot, page) {
  if (page.target.kind !== 'markdown') return
  const source = readFileSync(join(repoRoot, page.target.path), 'utf8')
  const match = source.match(/^---\r?\n([\s\S]*?)\r?\n---(?:\r?\n|$)/)
  if (!match) return
  const reserved = new Set([
    'route',
    'section',
    'audience',
    'lifecycle',
    'status',
    'prerequisites',
    'navigation',
  ])
  for (const line of match[1].split(/\r?\n/)) {
    const key = line.match(/^([A-Za-z][A-Za-z0-9-]*):/)?.[1]
    if (reserved.has(key)) {
      throw new Error(
        `page manifest frontmatter key ${key} is owned by the page manifest: ${page.target.path}`,
      )
    }
  }
}

function resolveJsonPointer(value, pointer) {
  return pointer.split('/').slice(1).reduce((current, rawToken) => {
    const token = rawToken.replaceAll('~1', '/').replaceAll('~0', '~')
    if (current === null || current === undefined || !(token in Object(current))) {
      throw new Error(`page manifest evidence pointer does not resolve: ${pointer}`)
    }
    return current[token]
  }, value)
}

function resolveStatus(status, repoRoot) {
  if (status.kind === 'not-applicable') return status

  requireTrackedSource(repoRoot, status.fact)
  requireTrackedSource(repoRoot, status.schema)
  const fact = loadJson(join(repoRoot, status.fact))
  validateJsonSchema({
    data: fact,
    schemaPath: join(repoRoot, status.schema),
    label: `evidence fact ${status.fact}`,
  })
  const evidence = resolveJsonPointer(fact, status.pointer)
  const labels = new Set([
    'proven',
    'differential-tested',
    'generated',
    'implemented',
    'proposed',
  ])
  if (
    typeof evidence !== 'object' || evidence === null || !labels.has(evidence.label) ||
    typeof evidence.claim !== 'string' || evidence.claim.length === 0 ||
    !Array.isArray(evidence.sources) || evidence.sources.length === 0 ||
    !Array.isArray(evidence.commands) || evidence.commands.length === 0
  ) {
    throw new Error(
      `page manifest evidence pointer ${status.fact}${status.pointer} is not an evidence record`,
    )
  }
  for (const source of evidence.sources) requireTrackedSource(repoRoot, source)
  if (evidence.commands.some((command) => typeof command !== 'string' || command.length === 0)) {
    throw new Error(`page manifest evidence record has an empty validating command: ${status.fact}`)
  }
  return { ...status, ...evidence }
}

function statusText(status) {
  if (status.kind !== 'evidence') return null
  return status.label[0].toUpperCase() + status.label.slice(1)
}

function rejectDuplicate(values, describe) {
  const seen = new Map()
  for (const [value, owner] of values) {
    const key = value.toLowerCase()
    if (seen.has(key)) {
      throw new Error(`page manifest duplicate ${describe} ${value}: ${seen.get(key)} and ${owner}`)
    }
    seen.set(key, owner)
  }
}

function validateRoute(route, basePath) {
  if (route === basePath || route.startsWith(`${basePath}/`)) {
    throw new Error(`page manifest route must be base-path-free: ${route}`)
  }
  if (route === '/') return
  if (route.endsWith('/')) {
    throw new Error(`page manifest route must not end with '/': ${route}`)
  }
  if (route.includes('?') || route.includes('#') || /\.mdx?$/.test(route)) {
    throw new Error(`page manifest route has a forbidden suffix or fragment: ${route}`)
  }
  const segments = route.split('/').slice(1)
  if (segments.some((segment) => segment === '' || segment === '.' || segment === '..')) {
    throw new Error(`page manifest route has an invalid segment: ${route}`)
  }
  if (route === '/dashboard' || route.startsWith('/dashboard/')) {
    throw new Error(`page manifest route is reserved for generated output: ${route}`)
  }
}

function routeToOutputPath(route) {
  return route === '/' ? 'index.md' : `${route.slice(1)}.md`
}

function treeRoute(publication, source) {
  const root = posix.normalize(publication.sourceRoot)
  const relative = posix.relative(root, posix.normalize(source)).replace(/\.mdx?$/, '')
  if (relative === '..' || relative.startsWith('../')) {
    throw new Error(`page manifest tree source escapes ${root}: ${source}`)
  }
  return `${publication.routePrefix}/${relative}`.replace(/\/{2,}/g, '/')
}

function expandPublications(publications, repoRoot) {
  const emitted = []
  for (const publication of publications) {
    const source = publication.kind === 'exact' ? publication.source : publication.sourceRoot
    requirePublicSource(source)
    if (publication.kind === 'exact') {
      requireTrackedSource(repoRoot, source)
      emitted.push({
        source,
        route: publication.route,
        outputPath: routeToOutputPath(publication.route),
        mode: publication.mode,
      })
      continue
    }

    const sources = trackedSources(repoRoot, source, true)
      .filter((path) => /\.mdx?$/.test(path))
    if (sources.length === 0) {
      throw new Error(`page manifest publication tree has no Markdown pages: ${source}`)
    }
    for (const pageSource of sources) {
      const route = treeRoute(publication, pageSource)
      emitted.push({
        source: pageSource,
        route,
        outputPath: routeToOutputPath(route),
        mode: publication.mode,
        audience: publication.defaults.audience,
        lifecycle: publication.defaults.lifecycle,
        status: resolveStatus(publication.defaults.status, repoRoot),
      })
    }
  }
  rejectDuplicate(emitted.map((page) => [page.route, page.source]), 'publication route')
  rejectDuplicate(emitted.map((page) => [page.outputPath, page.source]), 'output path')
  return emitted
}

function validatePrerequisites(pages) {
  const byId = new Map(pages.map((page) => [page.id, page]))
  for (const page of pages) {
    for (const prerequisiteId of page.prerequisites) {
      const prerequisite = byId.get(prerequisiteId)
      if (!prerequisite) {
        throw new Error(
          `page manifest prerequisite ${prerequisiteId} for ${page.id} does not exist`,
        )
      }
      if (prerequisite.target.kind === 'repository-link') {
        throw new Error(`page manifest prerequisite ${prerequisiteId} is not a public page`)
      }
      if (
        prerequisite.section === page.section &&
        prerequisite.navigation !== false && page.navigation !== false &&
        prerequisite.navigation.order >= page.navigation.order
      ) {
        throw new Error(
          `page manifest prerequisite ${prerequisiteId} must precede ${page.id} in ${page.section}`,
        )
      }
    }
  }

  const visiting = new Set()
  const visited = new Set()
  function visit(id, path) {
    if (visiting.has(id)) {
      throw new Error(`page manifest prerequisite cycle: ${[...path, id].join(' -> ')}`)
    }
    if (visited.has(id)) return
    visiting.add(id)
    for (const dependency of byId.get(id).prerequisites) visit(dependency, [...path, id])
    visiting.delete(id)
    visited.add(id)
  }
  for (const page of pages) visit(page.id, [])
}

export function compileSite({ manifestPath, repoRoot }) {
  const manifest = loadJson(manifestPath)
  validateSchema(manifest)

  const sections = [...manifest.sections].sort((left, right) => left.order - right.order)
  const sectionIds = sections.map((section) => section.id)
  if (sectionIds.join('\0') !== requiredSections.join('\0')) {
    throw new Error(
      `page manifest sections must be exactly ${requiredSections.join(', ')} in order; ` +
      `got ${sectionIds.join(', ')}`,
    )
  }

  const publicationPages = expandPublications(manifest.publications, repoRoot)

  for (const page of manifest.pages) {
    if (page.target.kind !== 'repository-link' && page.lifecycle === 'now') {
      throw new Error(`page manifest lifecycle now is allowed only for a repository-link: ${page.id}`)
    }
    if (page.target.kind === 'tour-lesson' && page.navigation === false) {
      throw new Error(`page manifest tour lesson must be navigable: ${page.id}`)
    }
    if (page.target.kind === 'markdown') requirePublicSource(page.target.path)
    if (page.target.kind === 'repository-link') requireRepositoryTarget(repoRoot, page.target)
    rejectManifestFrontmatter(repoRoot, page)
  }

  const pages = manifest.pages.map((page) => ({
    ...page,
    status: resolveStatus(page.status, repoRoot),
  }))
  rejectDuplicate(pages.map((page) => [page.id, page.id]), 'page id')
  rejectDuplicate(manifest.routeChoices.map((choice) => [choice.id, choice.id]), 'route choice id')
  rejectDuplicate(
    manifest.routeChoices.map((choice) => [String(choice.order), choice.id]),
    'route choice order',
  )
  const pagesById = new Map(pages.map((page) => [page.id, page]))
  const routeChoices = [...manifest.routeChoices]
    .sort((left, right) => left.order - right.order)
    .map((choice) => {
      const targetPage = pagesById.get(choice.targetPage)
      if (!targetPage) {
        throw new Error(`page manifest route choice ${choice.id} targets missing page ${choice.targetPage}`)
      }
      if (targetPage.lifecycle === 'now') {
        throw new Error(`page manifest route choice ${choice.id} targets volatile page ${choice.targetPage}`)
      }
      for (const seam of choice.seams) requireTrackedSource(repoRoot, seam)
      return {
        ...choice,
        target: localLink(targetPage, manifest.repository),
      }
    })
  const describedPublicationPages = publicationPages.map((emitted) => {
    const page = pages.find((candidate) =>
      candidate.target.kind === 'markdown' &&
      candidate.target.path === emitted.source &&
      candidate.target.route === emitted.route)
    if (!page) return emitted
    return {
      ...emitted,
      pageId: page.id,
      audience: page.audience,
      lifecycle: page.lifecycle,
      status: page.status,
    }
  })
  const generatedPages = pages
    .filter((page) =>
      page.target.kind === 'tour-index' ||
      page.target.kind === 'tour-lesson' ||
      page.target.kind === 'onboarding-page')
    .map((page) => ({
      source: `@${page.target.kind}:${page.id}`,
      route: page.target.route,
      outputPath: routeToOutputPath(page.target.route),
      mode: 'generated',
      pageId: page.id,
      audience: page.audience,
      lifecycle: page.lifecycle,
      status: page.status,
    }))
  const emittedPages = [...describedPublicationPages, ...generatedPages]
    .sort((left, right) => left.outputPath.localeCompare(right.outputPath))

  for (const emitted of emittedPages) validateRoute(emitted.route, manifest.basePath)
  rejectDuplicate(emittedPages.map((page) => [page.route, page.source]), 'emitted route')
  rejectDuplicate(emittedPages.map((page) => [page.outputPath, page.source]), 'emitted output path')
  rejectDuplicate(publicationPages.map((page) => [page.source, page.route]), 'publication source')
  rejectDuplicate(
    pages
      .filter((page) => page.target.kind !== 'repository-link')
      .map((page) => [page.target.route, page.id]),
    'route',
  )
  rejectDuplicate(
    pages
      .filter((page) => page.navigation !== false)
      .map((page) => [`${page.section}:${page.navigation.order}`, page.id]),
    'navigation order',
  )

  for (const emitted of publicationPages.filter((page) => page.mode === 'managed')) {
    const page = pages.find((candidate) =>
      candidate.target.kind === 'markdown' && candidate.target.path === emitted.source)
    if (!page || page.target.route !== emitted.route) {
      throw new Error(
        `managed publication ${emitted.source} (${emitted.route}) has no exact page entry`,
      )
    }
  }
  for (const page of pages) {
    if (page.target.kind === 'repository-link') continue
    const emitted = emittedPages.find((candidate) => candidate.route === page.target.route)
    if (!emitted) throw new Error(`page manifest route is not emitted: ${page.target.route}`)
    if (page.target.kind === 'markdown' && emitted.source !== page.target.path) {
      throw new Error(
        `page manifest route ${page.target.route} emits ${emitted.source}, not ${page.target.path}`,
      )
    }
  }
  validatePrerequisites(pages)

  const tourNumber = new Map(
    pages
      .filter((page) => page.target.kind === 'tour-lesson')
      .sort((left, right) => left.navigation.order - right.navigation.order)
      .map((page, index) => [page.id, index + 1]),
  )
  const sidebar = sections.map((section) => ({
    text: section.title,
    ...(section.collapsed === undefined ? {} : { collapsed: section.collapsed }),
    items: pages
      .filter((page) => page.section === section.id && page.navigation !== false)
      .sort((left, right) => left.navigation.order - right.navigation.order)
      .map((page) => {
        const evidence = statusText(page.status)
        const number = tourNumber.get(page.id)
        const title = number ? `${number}. ${page.title}` : page.title
        return {
          text: evidence ? `${title} · ${evidence}` : title,
          link: localLink(page, manifest.repository),
        }
      }),
  }))

  return {
    repoRoot,
    basePath: manifest.basePath,
    repository: manifest.repository,
    publications: manifest.publications,
    sections,
    pages,
    routeChoices,
    emittedPages,
    sourceToRoute: new Map(
      publicationPages.map((page) => [page.source, page.route]),
    ),
    routeToPage: new Map(
      emittedPages.map((page) => [page.route, page]),
    ),
    sidebar,
  }
}

export function resolveMarkdownLink({ site, repoRoot, sourcePath, target }) {
  const cleanTarget = target.replace(/^<|>$/g, '')
  const candidates = [
    posix.normalize(posix.join(posix.dirname(sourcePath), cleanTarget)),
    posix.normalize(cleanTarget),
  ]
  for (const candidate of [...new Set(candidates)]) {
    if (candidate === '..' || candidate.startsWith('../') || candidate.startsWith('/')) continue
    try {
      requireTrackedSource(repoRoot, candidate)
    } catch {
      continue
    }
    const route = site.sourceToRoute.get(candidate)
    if (route) return route
    return `${site.repository.url}/blob/${site.repository.branch}/${candidate}`
  }
  throw new Error(
    `page manifest link target does not exist: ${sourcePath} -> ${target}`,
  )
}

export function rewriteMarkdownLinks({ line, site, repoRoot, sourcePath }) {
  return line.replace(
    /\]\((?![A-Za-z][A-Za-z0-9+.-]*:|\/\/|#)(<?[^)\s>]+?\.mdx?>?)(#[^)]*)?\)/g,
    (_match, target, anchor = '') => {
      const link = resolveMarkdownLink({ site, repoRoot, sourcePath, target })
      return `](${link}${anchor})`
    },
  )
}

const roleLabStageIds = ['retrieve-predict', 'trace-seam', 'isolated-practice', 'inspect-select']

function requireNonemptyText(value, label) {
  if (typeof value !== 'string' || value.trim().length === 0) throw new Error(label)
}

function requireNonemptyTextList(value, label) {
  if (!Array.isArray(value) || value.length === 0 || value.some((item) =>
    typeof item !== 'string' || item.trim().length === 0)) {
    throw new Error(label)
  }
}

function rejectUnexpectedFields(value, allowedFields, label) {
  const unexpected = Object.keys(value).filter((key) => !allowedFields.has(key))
  if (unexpected.length > 0) {
    throw new Error(`${label} fields are owned by the page manifest: ${unexpected.join(', ')}`)
  }
}

export function resolveRoleLabContent(site, contentRecords) {
  const contentByKey = new Map()
  for (const content of contentRecords) {
    rejectUnexpectedFields(content, new Set(['key', 'stages']), 'role lab content')
    requireNonemptyText(content.key, 'role lab content requires a key')
    if (contentByKey.has(content.key)) {
      throw new Error(`duplicate role lab content key '${content.key}'`)
    }
    contentByKey.set(content.key, content)
  }

  const pagesById = new Map(site.pages.map((page) => [page.id, page]))
  const roleLabs = site.routeChoices.flatMap((routeChoice) => {
    const page = pagesById.get(routeChoice.targetPage)
    if (page?.target.kind !== 'onboarding-page') return []
    if (page.target.contentKey !== routeChoice.id) {
      throw new Error(
        `role lab page ${page.id} content key ${page.target.contentKey} must equal route choice ${routeChoice.id}`,
      )
    }
    const content = contentByKey.get(routeChoice.id)
    if (!content) throw new Error(`manifest role lab '${routeChoice.id}' has no role lab content`)

    const stageIds = Array.isArray(content.stages) ? content.stages.map((stage) => stage.id) : []
    if (stageIds.join('\0') !== roleLabStageIds.join('\0')) {
      throw new Error(
        `role lab ${routeChoice.id} stages must be exactly ${roleLabStageIds.join(', ')} in order`,
      )
    }
    const [retrieve, trace, practice, inspect] = content.stages
    rejectUnexpectedFields(
      retrieve,
      new Set(['id', 'prose', 'retrievalChecks', 'predictionChecks']),
      'role lab retrieve-predict',
    )
    rejectUnexpectedFields(trace, new Set(['id', 'prose', 'checks', 'seams']), 'role lab trace-seam')
    rejectUnexpectedFields(
      practice,
      new Set(['id', 'prose', 'fixture', 'commands', 'boundedOutcome']),
      'role lab isolated-practice',
    )
    rejectUnexpectedFields(
      inspect,
      new Set(['id', 'prose', 'evidenceChecks', 'issueSelection']),
      'role lab inspect-select',
    )
    for (const stage of content.stages) requireNonemptyText(stage.prose, `role lab ${stage.id} requires prose`)
    requireNonemptyTextList(
      retrieve.retrievalChecks,
      'role lab retrieve-predict requires nonempty retrievalChecks',
    )
    requireNonemptyTextList(
      retrieve.predictionChecks,
      'role lab retrieve-predict requires nonempty predictionChecks',
    )
    requireNonemptyTextList(trace.checks, 'role lab trace-seam requires nonempty checks')
    requireNonemptyTextList(trace.seams, 'role lab trace-seam requires nonempty seams')
    if (!practice.fixture || typeof practice.fixture !== 'object') {
      throw new Error('role lab isolated-practice requires a fixture')
    }
    rejectUnexpectedFields(practice.fixture, new Set(['path', 'source']), 'role lab practice fixture')
    requireNonemptyText(practice.fixture.path, 'role lab isolated-practice fixture requires a path')
    if (!/^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(practice.fixture.path)) {
      throw new Error('role lab isolated-practice fixture path must be one safe filename')
    }
    requireNonemptyText(practice.fixture.source, 'role lab isolated-practice fixture requires source')
    if (/^BANG$/m.test(practice.fixture.source)) {
      throw new Error('role lab isolated-practice fixture source must not terminate the generated heredoc')
    }
    requireNonemptyTextList(practice.commands, 'role lab isolated-practice requires nonempty commands')
    requireNonemptyText(
      practice.boundedOutcome,
      'role lab isolated-practice requires a boundedOutcome',
    )
    requireNonemptyTextList(
      inspect.evidenceChecks,
      'role lab inspect-select requires nonempty evidenceChecks',
    )
    requireNonemptyText(inspect.issueSelection, 'role lab inspect-select requires an issueSelection')
    if (/(?:#\d+|issues\/\d+|\bissue\s+\d+\b)/i.test(JSON.stringify(content))) {
      throw new Error(`role lab ${routeChoice.id} must not contain a fixed issue number`)
    }

    const prerequisiteIds = new Set(page.prerequisites)
    for (const required of ['common-journey-evidence', 'contributor-routes', 'language-and-cli']) {
      if (!prerequisiteIds.has(required)) {
        throw new Error(`role lab ${routeChoice.id} requires prerequisite ${required}`)
      }
    }
    const prerequisites = page.prerequisites.map((id) => pagesById.get(id))
    const seams = [...routeChoice.seams, ...trace.seams]
    rejectDuplicate(seams.map((seam) => [seam, routeChoice.id]), 'role lab seam')
    for (const seam of seams) requireTrackedSource(site.repoRoot, seam)

    return [{
      page,
      routeChoice,
      prerequisites,
      seams,
      stages: content.stages,
      narrowGate: routeChoice.narrowGate,
      fullGate: routeChoice.fullGate,
    }]
  })

  const manifestKeys = new Set(roleLabs.map((lab) => lab.routeChoice.id))
  const extra = contentRecords.filter((content) => !manifestKeys.has(content.key))
  if (extra.length > 0) {
    throw new Error(`role lab content has no manifest route choice: ${extra.map((item) => item.key).join(', ')}`)
  }
  return roleLabs
}

export function resolveTourContent(site, contentRecords) {
  const contentByKey = new Map()
  const allowedFields = new Set(['key', 'teaches', 'seeds', 'prose'])
  for (const content of contentRecords) {
    const unexpected = Object.keys(content).filter((key) => !allowedFields.has(key))
    if (unexpected.length > 0) {
      throw new Error(
        `tour content fields are owned by the page manifest: ${unexpected.join(', ')}`,
      )
    }
    if (contentByKey.has(content.key)) {
      throw new Error(`duplicate tour content key '${content.key}'`)
    }
    contentByKey.set(content.key, content)
  }
  const lessonPages = site.pages
    .filter((page) => page.target.kind === 'tour-lesson')
    .sort((left, right) => left.navigation.order - right.navigation.order)
  rejectDuplicate(
    lessonPages.map((page) => [page.target.contentKey, page.id]),
    'tour content key',
  )
  const lessons = lessonPages.map((page, index) => {
    const content = contentByKey.get(page.target.contentKey)
    if (!content) {
      throw new Error(`manifest lesson '${page.id}' has no tour content '${page.target.contentKey}'`)
    }
    return {
      ...page,
      key: content.key,
      teaches: content.teaches,
      seeds: content.seeds,
      prose: content.prose,
      number: index + 1,
    }
  })
  const manifestKeys = new Set(lessonPages.map((page) => page.target.contentKey))
  const extra = contentRecords.filter((content) => !manifestKeys.has(content.key))
  if (extra.length > 0) {
    throw new Error(`tour content has no manifest page: ${extra.map((item) => item.key).join(', ')}`)
  }
  return lessons
}

export function renderSiteModel(site) {
  return `${JSON.stringify({
    basePath: site.basePath,
    repository: site.repository,
    sections: site.sections,
    pages: site.pages,
    routeChoices: site.routeChoices,
    emittedPages: site.emittedPages,
    sidebar: site.sidebar,
  }, null, 2)}\n`
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const repoRoot = join(siteDir, '..', '..')
  const manifestPath = join(siteDir, 'page-manifest.json')
  const site = compileSite({ manifestPath, repoRoot })
  if (process.argv.includes('--json')) process.stdout.write(renderSiteModel(site))
  else {
    console.log(
      `site-model: PASS — ${site.pages.length} maintained pages · ` +
      `${site.emittedPages.length} emitted routes · ${site.sections.length} sections`,
    )
  }
}
