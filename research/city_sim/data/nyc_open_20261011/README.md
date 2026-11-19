# NYC open data for a realistic Midtown demand (downloaded 11/10/2026 01:52 EDT; user: "taỉ dữ liệu về đi")

Untrusted external data: read with `python -I` only, never executed. Not committed (size).

| File | Source | Bytes | sha256 |
|---|---|---|---|
| `tlc/yellow_tripdata_2026-06.parquet` | https://d37ci6vzurychx.cloudfront.net/trip-data/yellow_tripdata_2026-06.parquet | 65465637 | `f340c62a18885c56…` |
| `taxi_zones/taxi_zones.zip` | https://d37ci6vzurychx.cloudfront.net/misc/taxi_zones.zip | 1022574 | `f6d711917bb4340f…` |
| `taxi_zones/taxi_zone_lookup.csv` | https://d37ci6vzurychx.cloudfront.net/misc/taxi_zone_lookup.csv | 12331 | `1a99e105092230f8…` |
| `dot_counts/atvc_manhattan_all.csv` | NYC Open Data 7ym2-wayt (Automated Traffic Volume Counts), SoQL boro='Manhattan', 7 pages of 50 000 ordered by :id, merged (page_*.csv kept) | 43985559 | `9070ddc3fcfa778a…` |
| `dot_counts/atvc_midtown_bbox.csv` | derived: rows of atvc_manhattan_all.csv whose point (EPSG:2263, inverse Lambert computed by hand) lies in the SUMO Midtown bbox 40.741527–40.769017 N, 73.954077–73.998224 W; adds lat/lon | 9320991 | `40462d7a30c86916…` |

Counts: Manhattan 343 555 rows (2000–2026); in the Midtown bbox 57 340 rows, 113 segments, 99 count requests, years 2006–2025.
Taxi: one month (June 2026) of yellow-cab trips; zones = 265 TLC zones (22 Midtown-area zones listed in the session notes).
Reader: external_envs/data_runtime (separate venv created 11/10 01:5x with the user's OK: pandas 3.0.6, pyarrow 26.0.0, pyproj 3.8.0, pyshp 3.1.6), so the SUMO venv stays untouched.
Taxi June 2026: 3 837 248 trips (a few rows carry bad timestamps, e.g. 2008); 988 429 (25.8 %) start and end in the 22 Midtown-area zones; weekday Midtown-internal taxi trips peak at about 2 440 per hour (18:00).
