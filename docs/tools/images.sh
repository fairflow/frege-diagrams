#!/bin/sh
# Regenerate every picture of the documentation (docs/images/) from source:
# the example figures (examples/basic.fgd), the figures of NOTATION.md
# (docs/notation.fgd) and the key to view A. CI runs this and checks that
# nothing changed, so the pictures always match the code (CONTRIBUTING.md).
set -e
cd "$(dirname "$0")/../.."
lake build framediag >/dev/null
T=_build/docimages
rm -rf "$T"
lake exe framediag "$T/plain" --fig examples/basic.fgd --no-pdf >/dev/null
lake exe framediag "$T/links" --fig examples/basic.fgd --no-pdf --links >/dev/null
lake exe framediag "$T/key" --no-pdf >/dev/null          # writes legend.svg, the key to view A
lake exe framediag "$T/notation" --fig docs/notation.fgd --no-pdf >/dev/null
D=docs/images
mkdir -p "$D"
rm -f "$D"/*.svg
cp "$T/key/legend.svg" "$D/key_A.svg"
for f in ex_composite ex_composite_B ex_trans ex_trans_B ex_or ex_or_B \
         legend_B legend_B2 legend_B3 legend_curried legend_conj legend_nested; do
  cp "$T/plain/$f.svg" "$D/$f.svg"
done
cp "$T/links/ex_composite_B.svg" "$D/ex_composite_B_links.svg"
cp "$T/links/ex_serial_B.svg" "$D/ex_serial_B_links.svg"
for f in n_states n_states_B n_order n_order_B; do
  cp "$T/notation/$f.svg" "$D/$f.svg"
done
echo "docs/images: $(ls "$D" | wc -l | tr -d ' ') pictures"
