# Field data (downloaded 08/10/2026, 04:53–04:54, with the user's permission)

**Not tracked by git:** the data files are excluded by `.gitignore` here; this README is tracked. Survey: `research/papers/audits/FIELD_DATA_SURVEY_20261008.md`.

| File | Source | Licence | sha256 |
|---|---|---|---|
| `ved/VED_DynamicData_Part1.7z` (82.7 MB) | https://github.com/gsoh/VED/raw/master/Data/ | Apache-2.0 | 44d53754fd39e196171ec09f123604375d0248d5c06a97d6695ef0e22a948c61 |
| `ved/VED_DynamicData_Part2.7z` (93.7 MB) | same | Apache-2.0 | a235c894e619a9e06b6c28c6e68593e26f4b168265cd2c45a0f3a43e646bc701 |
| `ved/VED_Static_Data_*.xlsx` | same | Apache-2.0 | — |
| `ngsim/Peachtree-Street-Atlanta-GA.zip` (50.7 MB) | data.transportation.gov dataset 8ect-6jqj, attachment 7244a8b5-… | public (US DOT) | 91b9b1d4ed1d261e8c525df536adc466b6844ff49dc6fb08b815c735fe072a2f |
| `ngsim/Lankershim-Boulevard-LosAngeles-CA.zip` (80.2 MB) | same dataset, attachment 62273322-… | public | 8c14c09b45993d4aa18bcada587757104d96ae36ba270d4e99777a104652b2b9 |
| `ngsim/Lankershim_Blvd_Metadata_Documentation.pdf` | same dataset | public | — |
| `tampa_spat/tampa_spat_sample.csv` (43.9 MB, 82,392 rows) | https://data.transportation.gov/resource/xn7c-yu2n.csv | CC BY-SA 4.0 | 8823bd8cb8079000c9074d4a6eef7d2137bc14a4dddf01858226dfd4e4fecddf |

**Known issues:**
- **Lankershim zip.** The server-side attachment is truncated: its first entry, the aerial photos (122.7 MB, stored), runs past the 80.2 MB file, so `unzip` cannot read the directory. The Lankershim trajectories (1,607,319 rows) are available through the Socrata API (`location = lankershim`) but are not downloaded. Its signal-timing files are inside the broken zip.
- **VED fuel signals.** The direct Fuel Rate PID is sparse. MAF-derived fuel cannot see deceleration fuel cut-off (see the protocol F2).

**Extracted:**
- `ngsim/peachtree/`: trajectories CSV, signal timing (`signal_timing/`) and the data-analysis zip.

**Pending:**
- The Hamburg SensorThings sample (F3) waits until the user has cleaned the disk.
