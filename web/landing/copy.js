// The page's only interactivity: copy the install command to the clipboard.
// Gesture: click (or Enter/Space on the focused button) -> clipboard write ->
// the aria-live #copy-status announces "Copied" for screen readers and shows it.
// Degrades safely: if the Clipboard API is unavailable, the command stays
// selectable in the code block, so the page never depends on JS to be useful.
(() => {
  const btn = document.getElementById("copy-btn");
  const cmd = document.getElementById("install-cmd");
  const status = document.getElementById("copy-status");
  if (!btn || !cmd || !status) return;

  let clear;
  btn.addEventListener("click", async () => {
    const text = cmd.textContent.trim();
    try {
      await navigator.clipboard.writeText(text);
      status.textContent = "Copied to clipboard.";
    } catch {
      status.textContent = "Copy failed — select the command manually.";
    }
    clearTimeout(clear);
    clear = setTimeout(() => (status.textContent = ""), 4000);
  });
})();
