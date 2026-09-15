# D05/D06 — hồ sơ nghiệm thu bước 1–4

Phạm vi theo đoạn giao worker cuối trong tài liệu đính kèm: matching minimax, chứng nhận hai pha, cận vật lý bỏ đầu vào `hp`, miền không rỗng và ngưỡng pha. Các bước adaptive A07/Γ là chặng tiếp theo, không được đánh dấu đã đóng trong hồ sơ này.

Trạng thái build cuối được ghi bằng máy tại `manifest.json`; chỉ nhận khi `complete = true`, mọi `accepted = true`, và source gốc không đổi trong lần kiểm tra cuối.

## Kết quả và toàn bộ giả thiết còn giữ

- `full_actual_minimax_certificates`: với `Region q j T`, có một trọng số hợp lệ cho hai quyết định `T`, `Tᶜ`, được chọn trước world, đạt cận trên đồng thời với mọi `A ∈ worlds q j`. Mọi policy ngẫu nhiên hữu hạn có trọng số không âm, tổng bằng 1 và quyết định `S.card = T.card` đều có một world đạt cận dưới. Không hạn chế policy phía dưới vào hai quyết định phía trên.
- `slopeBval_le_quarter`: `0 ≤ t ≤ 1`, `2 ≤ q`, `A.card = q+1`, `(others A j).card = q` suy ra `b ≤ 1/4`. `hp_from_physical` thêm `1 ≤ rho` và `T ∈ worlds q j` để suy ra `rho - 2b ≥ 1/2`.
- `physical_certified_threshold` (mới): đầu vào `q : ℕ`, `j : I (2*q+1)`, `T : Finset (I (2*q+1))`, `t rho : ℝ`; giả thiết `2 ≤ q`, `T ∈ worlds q j`, `0 ≤ t ≤ 1`, `1 ≤ rho ≤ 2`, và `1 ≤ ((q:ℝ)-1)*slopeBval t T j`. Kết luận ghép chứng nhận minimax thực với `V = 0 ↔ 2a - e/(q+1) ≤ rho`. Không nhận `hp`, cận minimax hoặc kết luận ngưỡng làm giả thiết.
- `exampleT_mem`, `example_coefficients`, `example_threshold`, `example_full_support` (mới): `q=8`, `j=17`, `T={i : Fin 18 | i.val < 9}`, `t=1/25`; ngưỡng chính xác `(562/225)*(24/25)^16` nằm giữa 1 và 2; mỗi điểm cube có trọng số dương. Bổ đề coefficients/threshold cho mọi `rho` thỏa `1 ≤ rho ≤ 2`.
- `example_active_certified` (mới): tại `rho=1`, cùng reference cụ thể trên, giá trị dương và có cả cận trên/cận dưới minimax; không còn giả thiết ngoài.
- `example_inactive_certified` (mới): tại `rho=2`, cùng reference, chứng nhận minimax có giá trị 0; không còn giả thiết ngoài.

Quy ước `I n = Fin (n+1)`: `I (2*8+1)` là `Fin 18`, không phải `Fin 17`.

## Source, compile, audit và provenance

Bản sửa MatchingMinimax, CertifiedPhaseValue, PhysicalBounds và PhaseWitness đã có sẵn trong repo khi bắt đầu lượt này; log cũ chưa được coi là nghiệm thu mới. Lượt này thêm `LeanD6ReferencePhysicalCertificateV1.lean` để ghép các kết quả và formalize reference cụ thể.

`rebuild.py` chụp nguyên source 32 module trong dependency closure, rebuild theo thứ tự phụ thuộc vào thư mục `build/` riêng. Source upstream không sửa. `LEAN_PATH` chỉ chứa thư mục rebuild và thư viện ngoài, không chứa thư mục `.olean` gốc. Vì vậy mỗi local dependency thực sự được dùng là kết quả compile source có hash trong manifest.

`finalize.py` compile module ghép mới bằng closure vừa rebuild, kiểm đủ tám tên audit và chỉ cho phép `propext`, `Classical.choice`, `Quot.sound`. Mỗi module có receipt ghi source SHA-256, `.olean` SHA-256, log SHA-256, command, exit, thời gian, và hash các dependency trực tiếp. Audit cuối là audit bắc cầu: không chấp nhận `sorryAx` hay tiên đề ngoài danh sách trên.

Compiler chạy trực tiếp binary Lean 4.34.0-rc2 đã cài, với các thư viện mà Lake project sử dụng. `toolchain.json` ghi phiên bản/hash compiler, hash lockfile và revision package. Thư viện ngoài (Mathlib và các package lock) dùng cache đã cài; không tuyên bố rebuild toàn bộ Mathlib từ source. Cả 32 local dependencies được rebuild từ source. Khi nghiệm thu xong, các `.olean` tương ứng được đồng bộ vào repo và kiểm hash lại; bản cũ khác hash được lưu trong `previous_oleans/`. Sáu module chính nhận log/receipt mới ở thư mục source. `installation.json` ghi kết quả đồng bộ.

Không chạy thêm thí nghiệm. Các log `draft*` là lần thử sửa proof, không phải receipt nghiệm thu. Kết quả cuối chỉ lấy từ log không có hậu tố `draft` và `manifest.json`.

## Phần còn thiếu và giới hạn

- Điều kiện mạnh `(q-1)b ≥ 1` vẫn còn; cận `b ≤ 1/4` không loại bỏ nó.
- Witness chứng minh miền không rỗng tại `q=8`; không chứng minh `q=8` là kích thước nhỏ nhất. Các nhận xét scan số trong source cũ không được coi là theorem.
- Chứng nhận phủ toàn bộ họ world của construction hiện tại; chưa có cận trên cho mọi hàm `F` cùng response và mixed-difference bound.
- Chưa đóng adaptive Γ: solver hữu hạn với định lượng sai số thư viện, nhân quả/đo được của tracker, loss do sai nhãn nhân độ dài epoch, stopping time, termination, kỳ vọng hữu hạn, hệ số Γ đúng đơn vị query và chế độ q tăng. Đây là các nghĩa vụ toán học của chặng sau, không phải lỗi Lean còn lại của đợt bước 1–4.
