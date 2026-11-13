#!/bin/sh
# Downloads the external data that the round scripts read, into ./data and ./qrng_dl. Run it from this directory.
set -e
mkdir -p data qrng_dl
# DESI DR2 BAO: means and covariance, as packaged by CobayaSampler/bao_data.
base=https://raw.githubusercontent.com/CobayaSampler/bao_data/master/desi_bao_dr2
for f in desi_gaussian_bao_ALL_GCcomb_mean.txt desi_gaussian_bao_ALL_GCcomb_cov.txt; do
  curl -sSL -o "data/$f" "$base/$f"
done
# ANU quantum random bits: Kavulich, Van Deren and Schlosshauer, Phys. Lett. A 388, 127032 (2021), Zenodo 4440318,
# CC BY 4.0. Only the first 30 MB of the 21 GB ANU.zip are fetched. Its first entry, anubits_1, is deflate-compressed
# binary whose data start at byte 55 (a 30-byte header, the 9-byte name and a 16-byte extra field).
curl -sSL -r 0-31457279 -o qrng_dl/anu_head.bin "https://zenodo.org/api/records/4440318/files/ANU.zip/content"
python3 -c "import zlib; b = open('qrng_dl/anu_head.bin', 'rb').read(); open('qrng_dl/anubits_1.prefix', 'wb').write(zlib.decompressobj(-15).decompress(b[55:]))"
echo "fetched: data/ (DESI DR2 BAO) and qrng_dl/anubits_1.prefix ($(wc -c < qrng_dl/anubits_1.prefix) bytes)"
