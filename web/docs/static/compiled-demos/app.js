import { runBangModule } from './runtime.js'

const picker = document.querySelector('#demo-picker')
const title = document.querySelector('#result-title')
const observed = document.querySelector('#observed')
const expected = document.querySelector('#expected')
const detail = document.querySelector('#detail')
const provenance = document.querySelector('#provenance')
const source = document.querySelector('#source')

function setStatus(status, message) {
  document.documentElement.dataset.status = status
  detail.dataset.status = status
  detail.textContent = message
}

async function runDemo(pack, demo) {
  setStatus('running', `Loading ${demo.title}…`)
  title.textContent = demo.title
  observed.textContent = '…'
  expected.textContent = demo.expectedOutput
  source.href = demo.sourceUrl
  try {
    const response = await fetch(`./${demo.artifact}`, { cache: 'no-store' })
    if (!response.ok) throw new Error(`artifact fetch returned HTTP ${response.status}`)
    const output = await runBangModule(await response.arrayBuffer())
    observed.textContent = output
    if (output !== demo.expectedOutput) {
      throw new Error('output mismatch: the artifact did not byte-match its committed oracle')
    }
    setStatus('passed', `PASS · ${demo.title} byte-matches its oracle`)
  } catch (error) {
    observed.textContent = error?.message ?? String(error)
    setStatus('failed', `REFUSED / ERROR · ${error?.message ?? String(error)}`)
  }
}

try {
  const response = await fetch('./manifest.json', { cache: 'no-store' })
  if (!response.ok) throw new Error(`manifest fetch returned HTTP ${response.status}`)
  const pack = await response.json()
  provenance.textContent = `${pack.builtFrom.commit.slice(0, 12)} · ${pack.builtFrom.bangVersion}`
  for (const demo of pack.demos) {
    const button = document.createElement('button')
    button.type = 'button'
    button.textContent = demo.title
    button.dataset.demo = demo.id
    button.addEventListener('click', () => {
      const url = new URL(location.href)
      url.searchParams.set('demo', demo.id)
      history.replaceState(null, '', url)
      void runDemo(pack, demo)
    })
    picker.append(button)
  }
  const requested = new URL(location.href).searchParams.get('demo')
  const selected = pack.demos.find((demo) => demo.id === requested) ?? pack.demos[0]
  if (!selected) throw new Error('manifest contains no demos')
  await runDemo(pack, selected)
} catch (error) {
  setStatus('failed', `REFUSED / ERROR · ${error?.message ?? String(error)}`)
}
