// build.mjs — the landing page "build" is a validate-and-stage step.
// The page is pure static HTML/CSS/JS (no framework, no bundler by design —
// one page does not earn build tooling). So "build" = assert the required
// assets exist, then copy them to dist/ as the deployable artifact. It exits
// non-zero if anything is missing, so CI catches a broken page.
import { cpSync, mkdirSync, rmSync, existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(fileURLToPath(import.meta.url));
const dist = join(root, "dist");
const assets = ["index.html", "style.css", "copy.js"];

for (const a of assets) {
  if (!existsSync(join(root, a))) {
    console.error(`build FAILED: missing required asset ${a}`);
    process.exit(1);
  }
}

rmSync(dist, { recursive: true, force: true });
mkdirSync(dist, { recursive: true });
for (const a of assets) cpSync(join(root, a), join(dist, a));

console.log(`build OK: staged ${assets.length} assets -> dist/`);
