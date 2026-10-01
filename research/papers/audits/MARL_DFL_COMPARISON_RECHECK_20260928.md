# Phép đổi loss cần chứng minh điều gì — 28/09/2026

Đọc code: selector_train (features/Net/choose), selector_train_v3/v6, RUN_marl_e3_dfl.sh, PROTOCOL_E3_DFL, cheap_checks_v2_train, profile_cost. Không train, không sửa producer/protocol đang chạy.

## Thay đổi đề xuất

Giữ actor, inputs hợp lệ, nhãn continuation, candidate family và byte accounting; đổi gradient MSE sang expected decision gain trên candidate khả thi có prefix. Đây chính là v6 worker đã viết. Chưa có kết quả DFL được đọc trong audit này. Không bảo đảm loss mới khắc phục generalization/information limits.

Cần sửa cách nói: loss expected gain không hoàn toàn chưa có trong assets. MARL_cheap_checks_v2_train.py:139 đã dùng loss này cho direct network ở protocol budget đồng nhất/MP2 cũ. v6 thử nó ở setting learned-actor/heterogeneous receiver khác. Không claim invention hoặc lần đầu trong toàn project.

## Ba phân biệt cần giữ

1. Direct budget-aware là một lớp chính sách; direct-MSE là một implementation. DFL-direct thắng direct-MSE là cải thiện cách học direct, không phải chứng minh bounded revision mạnh hơn direct.
2. Trong cùng feasible family, R1 là tập con của unrestricted direct. Với oracle thật, max_R1 value <= max_direct value. Lợi của một learned R1 nếu có phải đến từ regularization/sample efficiency/search overhead, được đo với comparator tương ứng.
3. Thắng MSE còn âm không đủ; giữ prefix bằng tau=+inf cho gain 0 không phải lợi ích selector, và bid vẫn bị tính tiền nếu đã mua.

## Hai confound cụ thể trong v6/protocol hiện tại

- DFL chỉ dùng feasible mask OK, MSE mean trên MỌI candidate. Reproduce v3 bằng v6--loss mse là kiểm implementation tốt, nhưng không chứng minh khác biệt chỉ là loại loss: còn có tập candidate tham gia gradient. Muốn nói objective gây cải thiện, thêm đối chứng MSE-feasible; giữ MSE-all làm baseline lịch sử. Không thay output/protocol cũ.
- DFL thử T=.1,.3,1; MSE một cấu hình. Cùng số epoch MỖI run không phải cùng total training compute hoặc tuning budget. Protocol đã công khai extra compute, vì vậy pilot có thể đọc với nhãn đó; trước claim 'same training cost' cần phép so tuning budget tương đương hoặc T cố định trước kết quả trong một comparison mới. Cùng số byte deployment vẫn có thể đúng; hai loại chi phí khác nhau.

Bộ so tối thiểu: prefix; MSE-all; MSE-feasible; DFL-feasible. Các arm learned chính giữ cùng bid/response input. Nếu claim bid là contribution, thêm DFL-no-bid / same-byte queue control từ cùng trainer; không so DFL-bid với MSE-no-bid rồi gán toàn bộ gain cho bid.

R1 vs direct dùng cùng objective/inputs/candidates; nếu muốn tối ưu riêng mỗi policy thì cho cả hai cơ hội tune bằng SELECT tương đương, không chọn tất cả checkpoint theo direct rồi xem đó là training tối ưu cho R1.

## Đánh giá và cách đi tiếp

Pilot trên dữ liệu sẵn có: chosen gain >0 so prefix VÀ gain hơn strongest matched direct comparator, báo traffic-seed CI, harm, oracle regret và actual charged bytes. Nếu mục tiêu là đánh giá DFL-direct như implementation mới thì comparator là các direct implementations còn lại; không gọi thắng toàn lớp direct.

T/epoch/tau chọn SELECT; deployment dùng lựa chọn deterministic/threshold đã khai báo, không chỉ lấy expected softmax training gain làm kết quả. Code hiện pick_tau và dev_chosen đã dùng deterministic selection; giữ parity đó trong closed-loop v5. Không diễn giải logits DFL như value estimates hoặc lấy quantile của chúng làm epsilon certificate SafeEdit.

Nếu pilot dương: áp recipe đã chốt trên scratch actors 0–4, dùng same-actor prefix/direct; chạy closed loop, kiểm waiting cùng throughput/unfinished và actual bytes. Offline H=3 gain chưa là long-run benefit. Chỉ freeze final seeds khi development đọc xong; không dùng final để chọn temp/cap/actor.

Nếu DFL-direct tốt còn R1 không hơn nó: kể phương pháp direct lựa chọn theo gain; giữ revision là theory/ablation. Nếu DFL chỉ không sửa, hoặc vẫn kém direct matched, chưa đạt method benefit. Không hạn chế direct nhân tạo hoặc thêm thông tin privileged để tạo win. Cùng học actor–scheduler là một extension lớn khác, không tự suy ra cần làm từ negative của pilot nhỏ này.

Đây là một phương án sửa thuật toán có kiểm soát, không là chứng nhận novelty hay hứa kết quả dương. Không mở thêm simulator/actor architecture cho phép thử này.
