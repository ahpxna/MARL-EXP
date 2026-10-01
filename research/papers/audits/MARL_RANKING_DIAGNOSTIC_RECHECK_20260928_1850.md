# Kiểm lại diagnostic xếp hạng — 28/09/2026, 18:50 EDT

Phạm vi: đọc producer ranking/additive/selector diagnostic, bốn JSON ranking, JSON additive scratch, suy luận lại sáu checkpoint legal trên 48 DEV state/actor; đọc manifest dense/mix. Không train hoặc rollout lại, không sửa producer đang chạy, không mở final test. Các khoảng tin cậy dưới đây là chẩn đoán trên DEV, không phải kiểm định confirmatory.

## 1. Lỗi có thật: quy tắc xử lý hòa không thống nhất

`scripts/MARL_e3_ranking_diag.py:pair_stats` tính critic bằng `mean(da > 0)` trên các cặp có `dy > 0`. Dự đoán hòa nhận 0 điểm. Cùng hàm tính fewer-edits bằng `P(dn < 0) + .5 P(dn == 0)`. `acc_equal_edit_size` và `acc_big_differences` cũng dùng cách tính strict cho critic. `scripts/MARL_e3_selector_diag_v2.py:assess` có cùng strict pair metric; Spearman của v2 đã xử lý hòa đúng, không bị lỗi này.

Strict accuracy có thể dùng nếu ghi rõ, nhưng không được so với baseline random 0.5 hoặc heuristic có tie-half credit. Nếu mọi dự đoán hòa, metric strict cho 0, dù không có đảo chiều nào. Để so thứ tự nhất quán:

    pair_acc = P(pred_diff > 0 | true_diff > 0)
               + 0.5 P(pred_diff == 0 | true_diff > 0)

Báo thêm tie fraction. Không dùng epsilon tùy tiện để biến gần-hòa thành hòa.

### Tính lại legal DEV (3 initialization checkpoint mỗi actor)

Macro average theo state; sau đó average ba checkpoint. Bootstrap gom cả load/snapshot theo 8 traffic seed, giữ các checkpoint trong cùng cluster.

| actor | s0 | s1 | s2 | mean | CI 95% theo traffic seed | fewer-edits |
|---|---:|---:|---:|---:|---:|---:|
| scratch s3 | .5162 | .4878 | .4822 | .4954 | [.4823,.5090] | .5294 |
| BC s3 | .5155 | .5243 | .5393 | .5264 | [.4860,.5671] | .5566 |

Tỷ lệ prediction ties trên scratch: .0637/.0688/.1656; BC: .0798/.1540/.0266.
CI của chênh critic trừ fewer-edits: scratch [-.0815,+.0103], BC [-.0414,-.0177]. Đây là bất định theo traffic seed, có điều kiện trên actor và các checkpoint đang xét; không phải kết quả qua nhiều seed train actor.

Phải rút kết luận “critic đảo chiều có hệ thống”. Kết quả sửa gần chance và cả hai CI accuracy chứa .5. BC vẫn kém fewer-edits trong chẩn đoán này; scratch chưa chứng minh được chênh lệch. Không đổi dấu critic dựa trên kết quả cũ.

Lỗi này KHÔNG đổi profile được chọn, gain, oracle regret hoặc kết quả closed loop đã lưu. Selector vẫn chưa chứng minh cải thiện. Khoảng cách train–DEV vẫn đáng điều tra, nhưng train phải được chấm lại cùng metric. Ranking JSON đang dùng 300 state đầu theo thứ tự loader, không phải toàn bộ train.

## 2. Additive probe mới: có kết quả scratch, chưa có BC lúc đọc

Producer: `scripts/MARL_e3_additive_transfer.py`; artifact: `research/marl_budget/e3_additive_transfer_scratch_s3.json`.
768 train state, hai nửa 384/384 chia theo traffic seed. Mô hình cộng các chỉ báo thêm/bỏ sender cho từng receiver, ridge lambda 1/10/100. Prefix dự đoán gain zero, đúng mục tiêu gain tương đối. Pair metric ở script này đã cho hòa nửa điểm.

| transfer | overall | equal edit count |
|---|---:|---:|
| train -> DEV | .520 | .512 |
| train -> SELECT | .513 | .526 |
| half A -> B | .516 | .511 |
| half B -> A | .514 | .509 |
| train -> train | .532 | .517 |
| DEV -> DEV (in sample) | .568–.569 | .519 |

Các lambda gần như giống nhau. Có tín hiệu yếu; chưa có CI hay gain từ tập được chọn, nên chưa thể gọi là baseline thắng.

Docstring suy luận quá mạnh: additive thất bại KHÔNG chứng minh dữ liệu đảo chiều hoặc critic không thể học. Nó có thể thiếu context, interaction, support hoặc gặp noise. Additive thành công cũng không chứng minh nguyên nhân duy nhất là neural optimization. Mô hình này là phép thử baseline thấp chiều, không phải phép phân xử đầy đủ data-vs-model.

Hệ số riêng cũng không có diễn giải causal duy nhất: mỗi receiver thêm và bỏ cùng số sender, nên cộng c vào mọi hệ số add và trừ c khỏi mọi hệ số drop không đổi prediction. Ridge chọn một nghiệm nhưng correlation hệ số thấp không tự chứng minh effect reversal.

So sánh hiện chưa cùng tập khả thi: additive dùng +84 byte không bid; legal bid critic bị trừ chi phí bid. Cần common mask để so chẩn đoán, và đúng tổng byte để so deployment.

## 3. Mix vẫn có headroom trong họ đã đo

48 DEV label mix đã COMPLETE. Từ giá trị candidate đã lưu, max gain trung bình là +16.5 đơn vị waiting trên horizon H=3, dương 48/48 state (min 3, max 44); giống nhau với cap +84 hoặc +84 trừ 10 byte bid. Đây là oracle trong họ candidate, không phải selector hợp lệ, không phải % giảm waiting cả episode.

Vì vậy G1 no-message không có ý nghĩa thống kê không cho phép suy ra selector trên mix không có headroom. Nó cũng không chứng minh lợi ích học được: phải đợi selector.

## 4. Tiến trình lúc 18:49

Dense scratch s3: SELECT/DEV 304/304 COMPLETE; train shard 1/2/5 COMPLETE với 418/399/399 state. Shard 0/3/4 chưa có manifest COMPLETE. Chưa có kết quả F1 label dày.
Mix: SELECT/DEV 48/48 COMPLETE; ba train shard chưa có manifest COMPLETE. Chưa có kết quả selector mix.
Load average đọc được 38.89/56.56/59.05; con số ~78 là snapshot trước. Không dùng load average để suy ra CPU utilization hay tiến trình đã treo. Không khởi động thêm job.

## 5. Handoff theo thứ tự

1. Tạo version mới của ranking diagnostic, giữ nguyên JSON cũ; sửa tie credit cho overall/equal-size/big-difference ở cả ranking và selector diagnostic. Lưu tie rates, state-level rows, checkpoint hash và source hash. Phản ví dụ tối thiểu: predictor toàn hòa phải đạt .5, đảo thứ tự hoàn toàn 0, đúng hoàn toàn 1.
2. Chấm lại trên nhãn/checkpoint đã có, không rollout/train lại. Dùng cùng eligible masks cho so ranking và gom CI theo traffic seed. Rút câu “systematic inversion” khỏi notes/manuscript nếu đang dùng strict metric làm bằng chứng.
3. Hoàn tất additive probe đã có; chọn lambda và threshold bằng SELECT, không bằng DEV. Báo selected gain, oracle regret, harmful-edit rate và seed-cluster CI. Fewer-edits nếu dùng chọn trực tiếp sẽ chọn prefix, do đó pair accuracy tốt không tương đương gain dương. DEV->DEV chỉ là in-sample reference, không phải upper bound.
4. Hoàn tất dense/mix đang chạy; kiểm single writer, manifest, nguồn sinh nhãn và đầy đủ shard sau sự cố duplicate writer. Không mặc định resume thành công nghĩa là provenance đã sạch. Dense runner đã chết trước đây: cần xác nhận bước train/ablation được khởi động sau khi mọi shard COMPLETE; không mặc định tự chạy.
5. Dùng kết quả matched evaluation để quyết định selector, không mở thêm họ kiến trúc chỉ vì lỗi metric vừa phát hiện. Sau khi chọn trên development data, freeze actor/selector/baselines/threshold/bytes/endpoint rồi mới dùng final seeds. Actor scratch 5/5 đạt gate là tiến triển thật, nhưng headline method vẫn cần selector closed-loop improvement so với chính actor + prefix và direct baseline.
