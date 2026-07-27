#!/usr/bin/env bash
# EasyCrypt exporter fixture-mirror check.
#
# The EasyCrypt importer proves theorems about a COMMITTED literal rather than
# about a decoder application: the JSON decoders are well-founded recursive on a
# JSON size measure, so they have no kernel-reducible equations and a decoded
# value cannot be evaluated inside a proof (`CatCrypt/Crypto/EasyCryptImport/
# AGENTS.md`, "`#guard`, not `rfl`"). The golden `#guard`s therefore read the
# exporter's JSON with `include_str`, which needs a path inside this repository —
# so each exercised exporter fixture exists TWICE: once in the exporter's own
# `tests/` directory, and once mirrored into `CatCrypt/Crypto/EasyCryptImport/`.
#
# A stale mirror is silent. The Lean-side `#guard`s keep passing against the old
# bytes, so the importer stays green while it is pinned to an exporter output
# nobody produces any more — and the drift only surfaces the next time somebody
# regenerates, as a guard failure that looks unrelated to the change that caused
# it. This script is what makes that drift loud.
#
# FOUR dimensions, each FAILING (exit 1) on its own:
#
#   (1) MIRROR SYNC — every `*.expected.json` committed under the importer
#       directory is byte-equal to the exporter golden of the same name.
#       A difference means one copy was regenerated and the other was not:
#       re-run the exporter and copy the result to BOTH paths.
#
#   (2) MIRROR PROVENANCE — every mirrored golden has an exporter golden of the
#       same name AND an `.ec` source beside it. A mirror with no exporter
#       counterpart is a fixture that was hand-edited into the repo, which is
#       exactly the state the `#guard`s cannot detect.
#
#   (3) MIRROR REACHABILITY — every mirrored golden is read by an `include_str`
#       somewhere under the importer directory, and every `include_str` of a
#       `*.expected.json` resolves to a committed file. This catches an orphan
#       copy that no guard exercises (dead weight that still looks authoritative)
#       and a dangling include (which is a build error, reported here first).
#
#   (4) CLASSIFICATION — every `*.json` under the importer directory is either a
#       `*.expected.json` mirror, covered by (1)-(3), or is named in LEAN_ONLY
#       below. Dimensions (1)-(3) range over `*.expected.json` alone, so a
#       fixture committed under any other name is compared to no golden and need
#       not trace to an `.ec` source. Such a file can carry the exporter's
#       envelope — schema, version, source path, digest — while no exporter run
#       produced it, which is authoritative-looking text nothing checks.
#
# Exporter goldens that are NOT mirrored are reported, not failed: `globals` and
# `unsupported` exercise the export side only and have no Lean-side reader.
#
# The exporter is a separate repository, cloned as the sibling `../ec-export`.
# Override with EC_EXPORT_DIR. When it is absent the script reports that and
# exits 0 — there is nothing to compare against — so this is not a substitute for
# regenerating both copies after an exporter change.
#
# Run from anywhere in the repo: `bash scripts/ec-fixture-sync.sh`
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

IMPORT_DIR="CatCrypt/Crypto/EasyCryptImport"
EC_EXPORT_DIR="${EC_EXPORT_DIR:-../ec-export}"
EXPORT_TESTS="$EC_EXPORT_DIR/tests"

if [ ! -d "$IMPORT_DIR" ]; then
  echo "FAIL: importer directory not found: $IMPORT_DIR"
  exit 1
fi

if [ ! -d "$EXPORT_TESTS" ]; then
  echo "EasyCrypt exporter checkout not found at: $EC_EXPORT_DIR"
  echo "  Clone it as a sibling (../ec-export) or set EC_EXPORT_DIR, then re-run."
  echo "  Nothing to compare; skipping."
  exit 0
fi

FAILED=0

# Mirrored goldens: every `*.expected.json` committed on the importer side.
MIRRORED=()
while IFS= read -r f; do
  MIRRORED+=("$(basename "$f")")
done < <(find "$IMPORT_DIR" -name '*.expected.json' | sort)

# Exporter goldens.
GOLDENS=()
while IFS= read -r f; do
  GOLDENS+=("$(basename "$f")")
done < <(find "$EXPORT_TESTS" -maxdepth 1 -name '*.expected.json' | sort)

echo "Exporter goldens: ${#GOLDENS[@]} in $EXPORT_TESTS"
echo "Mirrored copies:  ${#MIRRORED[@]} in $IMPORT_DIR"
echo ""

# ---------------------------------------------------------------------------
# Dimension 1: mirror sync
# ---------------------------------------------------------------------------
echo "(1) MIRROR SYNC — mirrored golden is byte-equal to the exporter's"
DRIFTED=()
for name in "${MIRRORED[@]}"; do
  mirror="$IMPORT_DIR/$name"
  golden="$EXPORT_TESTS/$name"
  if [ ! -f "$golden" ]; then
    echo "    ?  $name  (no exporter golden — see dimension 2)"
  elif cmp -s "$golden" "$mirror"; then
    echo "    ok $name"
  else
    echo "    DRIFTED $name"
    DRIFTED+=("$name")
  fi
done

if [ "${#DRIFTED[@]}" -gt 0 ]; then
  echo ""
  echo "FAIL: ${#DRIFTED[@]} mirrored fixture(s) differ from the exporter golden."
  echo "      The importer's golden #guards are pinned to bytes the exporter no"
  echo "      longer produces (or to bytes it produces and the mirror predates)."
  echo "      Regenerate from the .ec source and write BOTH copies:"
  for name in "${DRIFTED[@]}"; do
    base="${name%.expected.json}"
    echo ""
    echo "        # in $EC_EXPORT_DIR, under the easycrypt opam switch"
    echo "        ./_build/default/bin/ec2json.exe -o tests/$name tests/$base.ec"
    echo "        cp tests/$name <repo>/$IMPORT_DIR/$name"
    echo "        diff --unified $EXPORT_TESTS/$name $IMPORT_DIR/$name"
  done
  echo ""
  echo "      Then rebuild CatCrypt.Crypto.EasyCryptImport.All to re-run the guards."
  echo "      A stamp shift across the whole file means the EasyCrypt installation"
  echo "      changed; see AGENTS.md, \"An EasyCrypt upgrade invalidates the fixtures\"."
  FAILED=1
fi
echo ""

# ---------------------------------------------------------------------------
# Dimension 2: mirror provenance
# ---------------------------------------------------------------------------
echo "(2) MIRROR PROVENANCE — mirrored golden traces to an exporter fixture"
ORPHAN_MIRROR=()
for name in "${MIRRORED[@]}"; do
  base="${name%.expected.json}"
  missing=""
  [ -f "$EXPORT_TESTS/$name" ] || missing="golden"
  if [ ! -f "$EXPORT_TESTS/$base.ec" ]; then
    missing="${missing:+$missing and }source"
  fi
  if [ -n "$missing" ]; then
    echo "    NO $missing  $name"
    ORPHAN_MIRROR+=("$name (no exporter $missing)")
  else
    echo "    ok $name  <- tests/$base.ec"
  fi
done

# Exporter goldens with no mirror: reported, not failed.
NOT_MIRRORED=()
for name in "${GOLDENS[@]}"; do
  [ -f "$IMPORT_DIR/$name" ] || NOT_MIRRORED+=("$name")
done
if [ "${#NOT_MIRRORED[@]}" -gt 0 ]; then
  echo "    export-side only (no Lean-side reader, not an error): ${NOT_MIRRORED[*]}"
fi

if [ "${#ORPHAN_MIRROR[@]}" -gt 0 ]; then
  echo ""
  echo "FAIL: ${#ORPHAN_MIRROR[@]} mirrored fixture(s) do not trace to the exporter:"
  printf '        %s\n' "${ORPHAN_MIRROR[@]}"
  echo "      A mirror whose .ec source or exporter golden is missing cannot be"
  echo "      regenerated, so nothing can ever confirm the exporter emits it: the"
  echo "      #guards over it pin the decoder against text of unknown origin. Add"
  echo "      the .ec source to the exporter's tests/ and regenerate, or delete the"
  echo "      copy together with its Lean-side reader."
  FAILED=1
fi
echo ""

# ---------------------------------------------------------------------------
# Dimension 3: mirror reachability
# ---------------------------------------------------------------------------
echo "(3) MIRROR REACHABILITY — mirrored golden is read by an include_str"
INCLUDED=()
DANGLING=()
while IFS= read -r hit; do
  src="${hit%%:*}"
  rel="${hit#*:}"
  resolved="$(cd "$(dirname "$src")" && printf '%s\n' "$(realpath -m "$rel")")"
  if [ -f "$resolved" ]; then
    INCLUDED+=("$(basename "$resolved")")
  else
    DANGLING+=("$src -> $rel")
  fi
done < <(grep -rhoE '^[^-]*include_str "[^"]*\.expected\.json"' --include='*.lean' "$IMPORT_DIR" \
         | sed -E 's/.*include_str "([^"]*)"/\1/' \
         | while IFS= read -r p; do printf '%s\n' "$p"; done \
         | sort -u \
         | while IFS= read -r p; do
             grep -rlF "include_str \"$p\"" --include='*.lean' "$IMPORT_DIR" \
               | while IFS= read -r s; do printf '%s:%s\n' "$s" "$p"; done
           done)

UNREAD=()
for name in "${MIRRORED[@]}"; do
  found=0
  for inc in ${INCLUDED[@]+"${INCLUDED[@]}"}; do
    if [ "$inc" = "$name" ]; then found=1; break; fi
  done
  if [ "$found" -eq 1 ]; then
    echo "    ok $name"
  else
    echo "    UNREAD $name"
    UNREAD+=("$name")
  fi
done

if [ "${#DANGLING[@]}" -gt 0 ]; then
  echo ""
  echo "FAIL: ${#DANGLING[@]} include_str path(s) do not resolve:"
  printf '        %s\n' "${DANGLING[@]}"
  FAILED=1
fi

if [ "${#UNREAD[@]}" -gt 0 ]; then
  echo ""
  echo "FAIL: ${#UNREAD[@]} mirrored fixture(s) are read by no include_str:"
  printf '        %s\n' "${UNREAD[@]}"
  echo "      The copy exists only to be kept in sync and no #guard exercises it."
  echo "      Either add the guard that reads it, or delete the copy — an"
  echo "      unexercised mirror is an authoritative-looking file nothing checks."
  FAILED=1
fi
echo ""

# ---------------------------------------------------------------------------
# Dimension 4: every JSON fixture under the importer is classified
# ---------------------------------------------------------------------------
# Dimensions 1-3 range over `*.expected.json`. A fixture committed under another
# name is invisible to all three: it is never compared to an exporter golden and
# never has to trace to an `.ec` source. Require every `*.json` here to be either
# a mirror or an explicitly declared Lean-side-only input.
echo "(4) CLASSIFICATION — every JSON fixture is a mirror or declared Lean-side"

# Lean-side-only inputs: hand-built JSON with no exporter fixture behind it.
# Add a name here only with a comment saying why it has no exporter counterpart.
LEAN_ONLY=()

UNCLASSIFIED=()
while IFS= read -r f; do
  name="$(basename "$f")"
  case "$name" in
    *.expected.json) echo "    ok $name  (mirror)" ; continue ;;
  esac
  declared=0
  for d in ${LEAN_ONLY[@]+"${LEAN_ONLY[@]}"}; do
    if [ "$d" = "$name" ]; then declared=1; break; fi
  done
  if [ "$declared" -eq 1 ]; then
    echo "    ok $name  (declared Lean-side-only)"
  else
    echo "    UNCLASSIFIED $name"
    UNCLASSIFIED+=("$name")
  fi
done < <(find "$IMPORT_DIR" -maxdepth 1 -name '*.json' | sort)

if [ "${#UNCLASSIFIED[@]}" -gt 0 ]; then
  echo ""
  echo "FAIL: ${#UNCLASSIFIED[@]} JSON fixture(s) escape dimensions 1-3:"
  printf '        %s\n' "${UNCLASSIFIED[@]}"
  echo "      A fixture not named '*.expected.json' is compared to no exporter"
  echo "      golden and need not trace to an .ec source. Either rename it to"
  echo "      '<base>.expected.json' and add the exporter fixture, or add it to"
  echo "      LEAN_ONLY in this script with a comment saying why none exists."
  FAILED=1
fi
echo ""

if [ "$FAILED" -ne 0 ]; then
  exit 1
fi

echo "OK: every mirrored EasyCrypt fixture matches its exporter golden, traces to"
echo "    an .ec source, and is read by a Lean-side include_str; every JSON"
echo "    fixture under the importer is classified."
