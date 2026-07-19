// The complete host boundary for the compiled demo pack: one stdout write import.
export function validateDemoImports(imports) {
  if (imports.length !== 1
      || imports[0].module !== 'wasi_snapshot_preview1'
      || imports[0].name !== 'fd_write'
      || imports[0].kind !== 'function') {
    throw new Error('refused: demo module must import only wasi_snapshot_preview1.fd_write')
  }
}

export function createStdoutWrite(getInstance, chunks) {
  return function fdWrite(fd, iovs, count, nwritten) {
    if (fd !== 1) throw new Error(`refused: fd_write descriptor ${fd}; stdout (1) only`)
    const memory = getInstance()?.exports?.memory
    if (!(memory instanceof WebAssembly.Memory)) {
      throw new Error('refused: demo module does not export WebAssembly memory')
    }
    const view = new DataView(memory.buffer)
    let total = 0
    for (let index = 0; index < count; index += 1) {
      const ptr = view.getUint32(iovs + index * 8, true)
      const length = view.getUint32(iovs + index * 8 + 4, true)
      chunks.push(new Uint8Array(memory.buffer.slice(ptr, ptr + length)))
      total += length
    }
    view.setUint32(nwritten, total, true)
    return 0
  }
}

export async function runBangModule(bytes) {
  const module = await WebAssembly.compile(bytes)
  validateDemoImports(WebAssembly.Module.imports(module))

  const chunks = []
  let instance
  const loaded = await WebAssembly.instantiate(module, {
    wasi_snapshot_preview1: {
      fd_write: createStdoutWrite(() => instance, chunks),
    },
  })
  instance = loaded
  if (typeof instance.exports._start !== 'function') {
    throw new Error('refused: demo module does not export _start')
  }
  instance.exports._start()

  const length = chunks.reduce((total, chunk) => total + chunk.length, 0)
  const output = new Uint8Array(length)
  let offset = 0
  for (const chunk of chunks) {
    output.set(chunk, offset)
    offset += chunk.length
  }
  return new TextDecoder('utf-8', { fatal: true }).decode(output)
}
