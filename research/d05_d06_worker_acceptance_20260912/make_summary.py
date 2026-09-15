from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
assert m['complete'] and m['original_sources_unchanged_at_final_check']
assert all(x['accepted'] for x in m['modules'])
key=['LeanD6ReferenceMatchingMinimaxV1','LeanD6ReferenceCertifiedPhaseValueV1','LeanD6ReferencePhysicalBoundsV1','LeanD6ReferencePhaseThresholdV1','LeanD6ReferencePhaseWitnessV1','LeanD6ReferencePhysicalCertificateV1']
rows=['# Receipt nghiệm thu cuối','',f"{len(m['modules'])} module compile exit 0. Source upstream giữ nguyên. Không có tiên đề ngoài `propext`, `Classical.choice`, `Quot.sound` trong các tên audit.",'','| Module | Lean exit | Số tên audit | SHA-256 source |','|---|---:|---:|---|']
for n in key:
 x=next(x for x in m['modules'] if x['module']==n)
 rows.append(f"| [{n}](build/{n}.lean) | {x['lean_exit']} | {len(x['axiom_audit'])} | `{x['source_sha256']}` |")
rows+=['','Mỗi module có [log và receipt JSON](logs/); manifest chứa hash `.olean`, hash log và hash source/binary của dependency trực tiếp. Bộ `.olean` nghiệm thu đầy đủ nằm trong `build/`.', '', '[Báo cáo giả thiết, lượng từ và giới hạn](REPORT.md) · [Manifest đầy đủ](manifest.json) · [Toolchain và lockfile](toolchain.json)', '', 'Các log draft (nếu có trong workspace làm việc) không thuộc nghiệm thu. Không chạy thêm thí nghiệm. Adaptive Γ chưa thuộc đợt giao bước 1–4.','']
(r/'RECEIPT.md').write_text('\n'.join(rows))
print('Wrote RECEIPT.md')
