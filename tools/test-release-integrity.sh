#!/usr/bin/env bash
# tool: role=test couples=tools/install.sh,tools/release-manifest.sh,.github/workflows/release.yml runs-in=verify
# Local, network-free falsification poles for release manifest generation and atomic,
# checksum-verifying installation.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
work="$(mktemp -d --tmpdir bang-release-integrity-XXXXXX)"
trap 'rm -rf "$work"' EXIT
checks=0

check() {
  local label="$1" expected="$2" actual="$3"
  checks=$((checks + 1))
  if [ "$expected" != "$actual" ]; then
    echo "FAIL $label: expected [$expected], got [$actual]" >&2
    exit 1
  fi
  echo "  ok   $label"
}

sha() {
  local line
  if command -v sha256sum >/dev/null 2>&1; then
    line="$(sha256sum "$1")"
  else
    line="$(shasum -a 256 "$1")"
  fi
  printf '%s' "${line%%[[:space:]]*}"
}

echo '── release manifest ──'
assets="$work/assets"
mkdir -p "$assets"
for triple in aarch64-darwin aarch64-linux x86_64-linux; do
  printf 'payload-%s' "$triple" > "$assets/bang-v1.2.3-$triple"
done
bash tools/release-manifest.sh v1.2.3 "$assets" >/dev/null
expected="$(
  for triple in aarch64-darwin aarch64-linux x86_64-linux; do
    file="bang-v1.2.3-$triple"
    printf '%s  %s\n' "$(sha "$assets/$file")" "$file"
  done
)"
check manifest-fixed-order "$expected" "$(cat "$assets/SHA256SUMS")"
cp "$assets/SHA256SUMS" "$work/first-manifest"
bash tools/release-manifest.sh v1.2.3 "$assets" >/dev/null
check manifest-deterministic "$(cat "$work/first-manifest")" "$(cat "$assets/SHA256SUMS")"

printf 'sentinel\n' > "$assets/SHA256SUMS"
printf 'unexpected\n' > "$assets/bang-v1.2.3-extra-platform"
set +e
bash tools/release-manifest.sh v1.2.3 "$assets" >"$work/manifest-extra.out" 2>&1
code=$?
set -e
check manifest-extra-fails 1 "$code"
check manifest-extra-preserves-old sentinel "$(cat "$assets/SHA256SUMS")"
rm "$assets/bang-v1.2.3-extra-platform"

printf 'sentinel\n' > "$assets/SHA256SUMS"
rm "$assets/bang-v1.2.3-aarch64-linux"
set +e
bash tools/release-manifest.sh v1.2.3 "$assets" >"$work/manifest-fail.out" 2>&1
code=$?
set -e
check manifest-missing-fails 1 "$code"
check manifest-failure-preserves-old sentinel "$(cat "$assets/SHA256SUMS")"

echo '── atomic installer ──'
fakebin="$work/fakebin"
mkdir -p "$fakebin"
cat > "$fakebin/uname" <<'EOF'
#!/usr/bin/env bash
case "$1" in
  -s) echo Linux ;;
  -m) echo x86_64 ;;
  *) exit 2 ;;
esac
EOF
cat > "$fakebin/fetch" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
url="$1"
dest="${2:-}"
printf '%s\n' "$url" >> "$FETCH_LOG"

case "$url" in
  https://api.github.com/repos/phibkro/bang/releases/latest)
    [ "$SCENARIO" != api-fail ] || exit 7
    if [ "$SCENARIO" = duplicate-tag ]; then
      printf '{\n  "tag_name": "v1.2.3",\n  "tag_name": "v1.2.4"\n}\n'
    else
      printf '{\n  "tag_name": "v1.2.3"\n}\n'
    fi
    ;;
  https://github.com/phibkro/bang/releases/download/v1.2.3/SHA256SUMS)
    [ -n "$dest" ] || exit 90
    [ "$SCENARIO" != missing-manifest ] || exit 22
    case "$SCENARIO" in
      malformed-manifest)
        printf 'not-a-checksum\n' > "$dest"
        ;;
      wrong-platform)
        {
          printf '%s  bang-v1.2.3-aarch64-darwin\n' "$EXPECTED_SHA"
          printf '%s  bang-v1.2.3-aarch64-linux\n' "$EXPECTED_SHA"
        } > "$dest"
        ;;
      duplicate-record)
        {
          printf '%s  bang-v1.2.3-aarch64-darwin\n' "$EXPECTED_SHA"
          printf '%s  bang-v1.2.3-aarch64-linux\n' "$EXPECTED_SHA"
          printf '%s  bang-v1.2.3-x86_64-linux\n' "$EXPECTED_SHA"
          printf '%s  bang-v1.2.3-x86_64-linux\n' "$EXPECTED_SHA"
        } > "$dest"
        ;;
      *)
        {
          printf '%s  bang-v1.2.3-aarch64-darwin\n' "$EXPECTED_SHA"
          printf '%s  bang-v1.2.3-aarch64-linux\n' "$EXPECTED_SHA"
          printf '%s  bang-v1.2.3-x86_64-linux\n' "$EXPECTED_SHA"
        } > "$dest"
        ;;
    esac
    ;;
  https://github.com/phibkro/bang/releases/download/v1.2.3/bang-v1.2.3-x86_64-linux)
    [ -n "$dest" ] || exit 91
    case "$SCENARIO" in
      binary-fail) exit 22 ;;
      interrupted) printf 'partial' > "$dest"; exit 56 ;;
      corrupt) printf 'corrupt-binary' > "$dest" ;;
      target-race)
        rm -f "$RACE_TARGET"
        mkdir "$RACE_TARGET"
        printf 'race-sentinel' > "$RACE_TARGET/keep"
        cp "$GOOD_BINARY" "$dest"
        ;;
      *) cp "$GOOD_BINARY" "$dest" ;;
    esac
    ;;
  *) echo "unexpected fake URL: $url" >&2; exit 92 ;;
esac
EOF
chmod +x "$fakebin/uname" "$fakebin/fetch"

good="$work/good-bang"
printf '#!/bin/sh\necho new-bang\n' > "$good"
good_sha="$(sha "$good")"

run_case() {
  local scenario="$1" want_success="$2"
  local home="$work/home-$scenario" install="$work/install-$scenario"
  mkdir -p "$home" "$install"
  printf 'existing-install' > "$install/bang"
  chmod 0755 "$install/bang"
  : > "$work/fetch-$scenario.log"
  set +e
  PATH="$fakebin:$PATH" \
    HOME="$home" \
    BANG_INSTALL_DIR="$install" \
    BANG_INSTALL_FETCH="$fakebin/fetch" \
    SCENARIO="$scenario" \
    FETCH_LOG="$work/fetch-$scenario.log" \
    EXPECTED_SHA="$good_sha" \
    GOOD_BINARY="$good" \
    RACE_TARGET="$install/bang" \
    bash tools/install.sh >"$work/install-$scenario.out" 2>&1
  local code=$?
  set -e

  if [ "$want_success" = yes ]; then
    check "$scenario-exit" 0 "$code"
    check "$scenario-content" "$(cat "$good")" "$(cat "$install/bang")"
    check "$scenario-executable" yes "$([ -x "$install/bang" ] && echo yes || echo no)"
    check "$scenario-tagged-url" 1 "$(grep -c '/download/v1.2.3/bang-v1.2.3-x86_64-linux$' "$work/fetch-$scenario.log")"
  else
    check "$scenario-fails" yes "$([ "$code" -ne 0 ] && echo yes || echo no)"
    check "$scenario-preserves-existing" existing-install "$(cat "$install/bang")"
  fi
  check "$scenario-cleans-temps" 0 "$(find "$install" -maxdepth 1 -type f -name '.bang-*' | wc -l | tr -d ' ')"
}

run_case valid yes
for scenario in corrupt missing-manifest wrong-platform interrupted binary-fail malformed-manifest duplicate-record api-fail duplicate-tag; do
  run_case "$scenario" no
done

# A directory (or symlink to one) must be rejected before fetching. Otherwise POSIX mv
# treats it as a destination directory and can falsely report a successful replacement.
directory_home="$work/home-directory-target"
directory_install="$work/install-directory-target"
mkdir -p "$directory_home" "$directory_install/bang"
printf 'nested-sentinel' > "$directory_install/bang/keep"
: > "$work/fetch-directory-target.log"
set +e
PATH="$fakebin:$PATH" \
  HOME="$directory_home" \
  BANG_INSTALL_DIR="$directory_install" \
  BANG_INSTALL_FETCH="$fakebin/fetch" \
  SCENARIO=valid \
  FETCH_LOG="$work/fetch-directory-target.log" \
  EXPECTED_SHA="$good_sha" \
  GOOD_BINARY="$good" \
  bash tools/install.sh >"$work/install-directory-target.out" 2>&1
code=$?
set -e
check directory-target-fails yes "$([ "$code" -ne 0 ] && echo yes || echo no)"
check directory-target-preserves-nested nested-sentinel "$(cat "$directory_install/bang/keep")"
check directory-target-fetches-nothing 0 "$(wc -l < "$work/fetch-directory-target.log" | tr -d ' ')"
check directory-target-cleans-temps 0 "$(find "$directory_install" -maxdepth 1 -type f -name '.bang-*' | wc -l | tr -d ' ')"

symlink_home="$work/home-symlink-directory-target"
symlink_install="$work/install-symlink-directory-target"
symlink_destination="$work/symlink-directory-destination"
mkdir -p "$symlink_home" "$symlink_install" "$symlink_destination"
printf 'linked-sentinel' > "$symlink_destination/keep"
ln -s "$symlink_destination" "$symlink_install/bang"
: > "$work/fetch-symlink-directory-target.log"
set +e
PATH="$fakebin:$PATH" \
  HOME="$symlink_home" \
  BANG_INSTALL_DIR="$symlink_install" \
  BANG_INSTALL_FETCH="$fakebin/fetch" \
  SCENARIO=valid \
  FETCH_LOG="$work/fetch-symlink-directory-target.log" \
  EXPECTED_SHA="$good_sha" \
  GOOD_BINARY="$good" \
  bash tools/install.sh >"$work/install-symlink-directory-target.out" 2>&1
code=$?
set -e
check symlink-directory-target-fails yes "$([ "$code" -ne 0 ] && echo yes || echo no)"
check symlink-directory-target-preserves-link yes "$([ -L "$symlink_install/bang" ] && echo yes || echo no)"
check symlink-directory-target-preserves-nested linked-sentinel "$(cat "$symlink_destination/keep")"
check symlink-directory-target-fetches-nothing 0 "$(wc -l < "$work/fetch-symlink-directory-target.log" | tr -d ' ')"
check symlink-directory-target-cleans-temps 0 "$(find "$symlink_install" -maxdepth 1 -type f -name '.bang-*' | wc -l | tr -d ' ')"

# Falsify the second target-type check by changing a regular target into a directory
# from inside the binary fetch. The downloaded, verified temp must not descend into it.
race_home="$work/home-target-race"
race_install="$work/install-target-race"
mkdir -p "$race_home" "$race_install"
printf 'existing-install' > "$race_install/bang"
: > "$work/fetch-target-race.log"
set +e
PATH="$fakebin:$PATH" \
  HOME="$race_home" \
  BANG_INSTALL_DIR="$race_install" \
  BANG_INSTALL_FETCH="$fakebin/fetch" \
  SCENARIO=target-race \
  FETCH_LOG="$work/fetch-target-race.log" \
  EXPECTED_SHA="$good_sha" \
  GOOD_BINARY="$good" \
  RACE_TARGET="$race_install/bang" \
  bash tools/install.sh >"$work/install-target-race.out" 2>&1
code=$?
set -e
check target-race-fails yes "$([ "$code" -ne 0 ] && echo yes || echo no)"
check target-race-preserves-directory yes "$([ -d "$race_install/bang" ] && echo yes || echo no)"
check target-race-preserves-sentinel race-sentinel "$(cat "$race_install/bang/keep")"
check target-race-does-not-descend 0 "$(find "$race_install/bang" -mindepth 1 -maxdepth 1 ! -name keep | wc -l | tr -d ' ')"
check target-race-cleans-temps 0 "$(find "$race_install" -maxdepth 1 -type f -name '.bang-*' | wc -l | tr -d ' ')"

echo "test-release-integrity: PASS — $checks checks hold."
