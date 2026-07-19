import { createHash } from 'node:crypto'
import { createReadStream, existsSync, readFileSync, readdirSync, statSync } from 'node:fs'
import { createServer } from 'node:http'
import { dirname, extname, join, normalize, sep } from 'node:path'
import { fileURLToPath } from 'node:url'
import { compileSite } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const publicDir = join(siteDir, 'dist', 'public')
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot,
})
if (!existsSync(join(publicDir, 'index.html'))) {
  throw new Error('site-smoke: dist/public is missing; run the production Vocs build first')
}
const demoDir = join(publicDir, 'demos', 'compiled')
const demoManifestPath = join(demoDir, 'manifest.json')
if (!existsSync(join(demoDir, 'index.html')) || !existsSync(demoManifestPath)) {
  throw new Error('site-smoke: compiled demo pack is missing from the built site')
}
const demoManifest = JSON.parse(readFileSync(demoManifestPath, 'utf8'))
for (const demo of demoManifest.demos) {
  const artifact = join(demoDir, demo.artifact)
  if (!existsSync(artifact)) throw new Error(`site-smoke: missing demo artifact ${demo.artifact}`)
  const actual = createHash('sha256').update(readFileSync(artifact)).digest('hex')
  if (actual !== demo.artifactSha256) {
    throw new Error(`site-smoke: deployed demo hash mismatch for ${demo.artifact}`)
  }
}

function contentType(path) {
  return ({
    '.css': 'text/css; charset=utf-8',
    '.html': 'text/html; charset=utf-8',
    '.js': 'text/javascript; charset=utf-8',
    '.json': 'application/json; charset=utf-8',
    '.wasm': 'application/wasm',
  })[extname(path)] ?? 'application/octet-stream'
}

function staticFile(pathname) {
  if (pathname !== site.basePath && !pathname.startsWith(`${site.basePath}/`)) return null
  const suffix = pathname.slice(site.basePath.length).replace(/^\/+/, '')
  const normalized = normalize(suffix || '.').split(sep).join('/')
  if (normalized === '..' || normalized.startsWith('../')) return null
  const candidates = suffix === ''
    ? [join(publicDir, 'index.html')]
    : [join(publicDir, normalized, 'index.html'), join(publicDir, normalized)]
  return candidates.find((candidate) => existsSync(candidate) && statSync(candidate).isFile()) ?? null
}

const server = createServer((request, response) => {
  const pathname = new URL(request.url, 'http://127.0.0.1').pathname
  const file = staticFile(pathname)
  if (!file) {
    response.writeHead(404, { 'content-type': 'text/plain' })
    response.end('not found')
    return
  }
  response.writeHead(200, {
    'content-type': contentType(file),
  })
  createReadStream(file).pipe(response)
})
await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
let browser

try {
  const address = server.address()
  const origin = `http://127.0.0.1:${address.port}`
  const localRoutes = site.emittedPages
  const repositoryItems = site.pages.filter((page) =>
    page.navigation !== false && page.target.kind === 'repository-link')

  const rendered = await Promise.all(localRoutes.map(async (page) => {
    const route = page.route === '/' ? `${site.basePath}/` : `${site.basePath}${page.route}`
    const response = await fetch(`${origin}${route}`)
    if (!response.ok) throw new Error(`site-smoke: ${route} returned HTTP ${response.status}`)
    const html = await response.text()
    if (!html.includes('<html')) throw new Error(`site-smoke: ${route} did not return HTML`)
    for (const match of html.matchAll(/href="(\/[^"#]*)/g)) {
      const href = match[1]
      if (href !== site.basePath && !href.startsWith(`${site.basePath}/`)) {
        throw new Error(`site-smoke: ${route} link escapes ${site.basePath}: ${href}`)
      }
    }
    return [page.route, html]
  }))
  const rootHtml = new Map(rendered).get('/')

  for (const section of site.sections) {
    if (!rootHtml.includes(section.title)) {
      throw new Error(`site-smoke: homepage omits section label '${section.title}'`)
    }
  }
  const configAssets = readdirSync(join(publicDir, 'assets'))
    .filter((name) => /^config-.*\.js$/.test(name))
  if (configAssets.length !== 1) {
    throw new Error(`site-smoke: expected one built Vocs config asset, found ${configAssets.length}`)
  }
  const builtConfig = readFileSync(join(publicDir, 'assets', configAssets[0]), 'utf8')
  for (const page of repositoryItems) {
    const expected = `${site.repository.url}/${page.target.view}/${site.repository.branch}/${page.target.path}`
    if (!builtConfig.includes(expected)) {
      throw new Error(`site-smoke: built navigation omits repository link ${expected}`)
    }
  }

  const builtHtmlCount = readFileSync(join(publicDir, 'index.html'), 'utf8').length
  if (builtHtmlCount < 1000) throw new Error('site-smoke: homepage HTML is unexpectedly sparse')

  const { default: puppeteer } = await import('puppeteer')
  browser = await puppeteer.launch({
    headless: true,
    executablePath: process.env.PUPPETEER_EXECUTABLE_PATH || undefined,
    args: ['--no-sandbox', '--disable-gpu', '--disable-dev-shm-usage'],
  })
  const browserPage = await browser.newPage()
  for (const demo of demoManifest.demos) {
    const route = `${site.basePath}/demos/compiled/?demo=${encodeURIComponent(demo.id)}`
    await browserPage.goto(`${origin}${route}`, { waitUntil: 'networkidle0' })
    await browserPage.waitForFunction(
      () => ['passed', 'failed'].includes(document.documentElement.dataset.status),
      { timeout: 30000 },
    )
    const result = await browserPage.evaluate(() => ({
      status: document.documentElement.dataset.status,
      detail: document.querySelector('#detail')?.textContent,
      observed: document.querySelector('#observed')?.textContent,
    }))
    if (result.status !== 'passed' || result.observed !== demo.expectedOutput) {
      throw new Error(`site-smoke: browser demo ${demo.id} failed: ${JSON.stringify(result)}`)
    }
  }
  console.log(
    `site-smoke: PASS — ${localRoutes.length} emitted routes served under ` +
    `${site.basePath} · ${repositoryItems.length} repository-only links present · ` +
    `${demoManifest.demos.length} compiled demos ran in Chromium`,
  )
} finally {
  if (browser) await browser.close()
  await new Promise((resolve, reject) => server.close((error) => error ? reject(error) : resolve()))
}
