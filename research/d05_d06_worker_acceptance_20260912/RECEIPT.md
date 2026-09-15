# Receipt nghiệm thu cuối

33 module compile exit 0. Source upstream giữ nguyên. Không có tiên đề ngoài `propext`, `Classical.choice`, `Quot.sound` trong các tên audit.

| Module | Lean exit | Số tên audit | SHA-256 source |
|---|---:|---:|---|
| [LeanD6ReferenceMatchingMinimaxV1](build/LeanD6ReferenceMatchingMinimaxV1.lean) | 0 | 12 | `3882d971d9ab2bf381b3b85318269b9dac9f3abb5b885b476ab35b6a9acef058` |
| [LeanD6ReferenceCertifiedPhaseValueV1](build/LeanD6ReferenceCertifiedPhaseValueV1.lean) | 0 | 4 | `39e15c349b2cd06e8a2e84e69fd7bf751311853d6a5bda8d103d7c482b12d530` |
| [LeanD6ReferencePhysicalBoundsV1](build/LeanD6ReferencePhysicalBoundsV1.lean) | 0 | 6 | `b912b202593b2f293352c68b0e1b1f502e666fb4d200f93bd3386023162bf394` |
| [LeanD6ReferencePhaseThresholdV1](build/LeanD6ReferencePhaseThresholdV1.lean) | 0 | 6 | `b89fe81acda50c8e3ae37565edf73e46e0d6fc52bd415879bfc48760c58c12ba` |
| [LeanD6ReferencePhaseWitnessV1](build/LeanD6ReferencePhaseWitnessV1.lean) | 0 | 20 | `5776fcfa6d0dcfa460465a84feee006a3c56ef9b60b449a42150493a7f470a58` |
| [LeanD6ReferencePhysicalCertificateV1](build/LeanD6ReferencePhysicalCertificateV1.lean) | 0 | 8 | `f1c8ca48c53aa29abe11c4f72bfc6ca0cb27fe3835a18da99748c5c0b109a95a` |

Mỗi module có [log và receipt JSON](logs/); manifest chứa hash `.olean`, hash log và hash source/binary của dependency trực tiếp. Bộ `.olean` nghiệm thu đầy đủ nằm trong `build/`.

[Báo cáo giả thiết, lượng từ và giới hạn](REPORT.md) · [Manifest đầy đủ](manifest.json) · [Toolchain và lockfile](toolchain.json)

Các log draft (nếu có trong workspace làm việc) không thuộc nghiệm thu. Không chạy thêm thí nghiệm. Adaptive Γ chưa thuộc đợt giao bước 1–4.
