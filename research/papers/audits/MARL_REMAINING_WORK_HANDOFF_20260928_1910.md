# Việc còn lại sau vòng diagnostic — 28/09/2026, 19:10 EDT

Phạm vi kiểm: đọc runner F1, scratch-panel, các runner gọi diagnostic, final protocol draft, current claims, ledger và các đoạn đang thiếu trong paper_marl.tex. Đây là kiểm đường găng, không chạy lại experiments, không xác nhận rằng mọi artifact trong repo đều đúng. Không sửa producer đang chạy hoặc framing thay tác giả.

## Kết luận

Đã xong một vòng chẩn đoán và sửa metric. Chưa xong development experiments, chưa freeze/final test, chưa đủ bằng chứng đạt đích method paper, chưa có bản gửi hoàn chỉnh. Không phải chỉ còn chờ.

## Việc worker làm ngay, không cần đợi label

### W1 — không để pipeline sinh lại diagnostic sai

Phát hiện hiện hành: sáu runner còn gọi MARL_e3_selector_diag_v2.py:
- RUN_marl_e3_dense_f1.sh:67;
- RUN_marl_e3_acq2.sh:13;
- RUN_marl_e3_priv_diag.sh:17;
- RUN_marl_e3_mix_downstream.sh:41;
- RUN_marl_e3_samebyte.sh:14;
- RUN_marl_e3_multi.sh:13.

v2 vẫn tính prediction ties bằng zero; v3 đã sửa. Scratch-panel dùng v3 là đúng. Trước lần chạy tiếp, owner chuẩn bị wrapper/runner version mới dùng v3 và output tên có version. Không sửa một shell script đang chạy mà chưa phối hợp owner; nếu job đã chạy thì giữ output cũ và hậu xử lý v3 từ checkpoint/labels đã lưu. Sửa đúng diagnostic không đổi algorithm/gain hoặc yêu cầu retrain. Không ghi đè JSON cũ.

Done: mọi artifact sẽ được đưa vào paper có metric version rõ, không đường future-run nào vô tình xuất strict metric như tie-half.

### W2 — bộ tổng hợp kết quả để dùng khi job hoàn tất

RUN_marl_e3_scratch_panel.sh hiện là summary phát triển: mean/range qua actor, chưa phải báo cáo thống kê cuối.

Chuẩn bị reporter nhận raw rows, tách actor-seed, selector-init, traffic-seed, load, method, cap, checkpoint-hash. Ghép cùng actor/cùng traffic; average selector init trong actor, không coi đó là actor replication. Báo từng actor và uncertainty có xét actor và traffic seed, giữ hai loads cùng traffic seed trong cluster. Tính waiting, actual total bytes, edits, harm, throughput/unfinished và travel-time censoring theo endpoint đã khai báo; nếu runner chưa ghi endpoint thì nêu thiếu, không tự suy từ waiting.

Assert đủ method/seed/cap, không thiếu/duplicate episode, bytes đúng, oracle chỉ diagnostic, model/checkpoint đúng recipe. Reporter phải lưu machine-readable summary và source manifest, không chỉ tee text.

Done: một bảng phân biệt actor-vs-MP2, selector-vs-same-actor-prefix, selector-vs-direct, bid-vs-same-byte-control. Chưa cần có đủ dữ liệu để viết và kiểm schema reporter.

### W3 — điền sẵn gói freeze F6

PROTOCOL_E3_FINAL_DRAFT vẫn DRAFT; actor list, proposed selector, primary endpoint type và hashes còn OPEN. Chuẩn bị manifest actor 0–4 scratch, selectors/comparators, candidate generator, normalization, bid bins, tau, runtime/source/config hashes, byte rules, evaluation seeds, failures/retries/censoring và cách thống kê. BC/mix giữ vai trò diagnostic theo gate, không đổi gate sau khi thấy gain.

Đề xuất endpoint cho đúng đích method hiện tại: superiority về waiting so với cùng actor + prefix tại một cap khai báo, kèm direct và guardrails. Nếu muốn claim tiết kiệm bytes/non-inferiority phải có tradeoff thực, margin và cách kiểm tra chốt trước test; không tự chuyển endpoint chỉ để né kết quả âm.

Không ghi FROZEN hoặc mở 1301–1316 khi chưa có kết quả development và lựa chọn của tác giả. Việc quyết định scope/endpoint còn mở không ngăn worker hoàn tất tất cả phần kỹ thuật của gói này.

### W4 — hoàn tất phần manuscript/artifact không phụ thuộc kết quả

Đích vẫn là method MARL. Viết rõ các recipe và vai trò theory, E1, fixed MP2, learned actors; không lấy actor thắng MP2 làm bằng chứng selector. Bridge traffic là reduced/post-hoc object, không phải certified neural policy. Giữ correction history, đưa số cuối qua bảng truy xuất artifact.

Hoàn tất method, assumptions, comparator adaptations, bytes, split/seed protocol, limitations, reproducibility commands và figure templates. Paper hiện vẫn có TODO final freeze/test, dense/mix/scratch frontier/shift, venue/author; abstract còn 9–23% trong khi claim map có actor tới 24.2%, cần thống nhất phạm vi/denominator khi viết cuối.

Nếu không làm đầy đủ network-delay của method thì giữ đúng nhãn receiver-observation stress test. Frontier/shift cần chạy nếu giữ claim đó; nếu phạm vi hẹp hơn, tác giả chọn bỏ claim, không giả vờ đã làm. Không thêm simulator hay theorem chỉ để lấp thời gian chờ.

## Việc phụ thuộc label/job

### W5 — khép development theo kế hoạch đã có

1. Dense: đủ tất cả manifest COMPLETE + audit nhãn/provenance sau resume và incident; một writer mỗi output. Chạy registered v2 ablation, rồi F1 comparison có same candidate table, original SELECT, matched update budget, full dense panel, acquisition v2. Những bước đó vẫn là train/evaluation còn lại, không phải label xong là xong.
2. Scratch: hoàn tất downstream s0/1/2/4, tổng hợp cả năm. Kiểm recipe/checkpoints thực thi: offline selector v3 và một closed-loop file tên v3 không tự chứng minh cùng thuật toán/checkpoint.
3. Mix: hoàn tất selectors rồi báo như diagnostic, vẫn giữ G1 FAIL. Oracle headroom +16.5 không chứng minh learned gain.
4. BC s2/s4: giữ kết quả descriptive, recipe pilot FAIL không tự được nâng thành method vì seed sau tốt.

Done: bảng trả lời rõ data density, acquisition và actor distribution có cải thiện selected gain/closed loop hay không. So paired, đúng cost; CI chứa zero không là equivalence.

### W6 — quyết định recipe và đánh giá cuối

Nếu một recipe legal có tín hiệu: xác nhận nó đúng algorithm ở runtime, dùng cùng recipe trên các actor thuộc claim, so same-byte baselines. Kết quả dương chỉ trên scratch s3 chưa tự thành benefit across five actors. Chọn hyperparameters theo SELECT; development dùng theo scope đã khai báo. Freeze rồi chạy fresh final panel đúng một lần.

Nếu mọi nhánh đã đăng ký vẫn âm: báo đích method CHƯA đạt. Không mở final test để tìm may mắn, không tự bỏ CityFlow hoặc đổi thành analysis paper. Tác giả/thầy quyết một extension có giả thuyết và ngân sách rõ, hoặc thay scope bài nộp. Không thêm vô hạn kiến trúc để săn điểm dương.

Sau final: viết lại abstract/results/conclusion theo kết quả, hoàn thiện figures, kiểm PDF và template/anonymity khi track đã xác nhận, đóng artifact manifest và reproducibility. Commit/backup theo ủy quyền của tác giả; không chỉ dựa vào untracked files để bàn giao.

## Thứ tự giao worker

Ngay: W1 -> W2 -> W3 -> W4, giữ nguyên các job đã có.
Khi dữ liệu xong: W5 -> quyết định W6 -> final report/PDF/artifact.
Không cần thêm diagnostics rộng ở thời điểm này. Chờ chỉ là trạng thái của W5, không phải của toàn dự án.
