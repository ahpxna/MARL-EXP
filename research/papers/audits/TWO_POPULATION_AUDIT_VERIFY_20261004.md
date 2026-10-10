# Verify audit "TWO_POPULATION_DESTINATION_AND_REOPENING_20261004" (04/10/2026 01:4x EDT)

Nguồn: review do user dán lúc 01:3x, cùng file `/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/TWO_POPULATION_DESTINATION_AND_REOPENING_20261004.md`.

Đã kiểm:
- code `scripts/CITY_q7_cross_version.py`, `scripts/CITY_env.py`;
- `q7b_contract_20261002/report.txt`;
- ledger city C-1 … C-10;
- checkpoint hiện có;
- tìm văn liệu có mục tiêu: 7 truy vấn, đọc mức abstract/kết quả, **chưa đọc sâu**.

Không chạy mô phỏng nào.

## 1. Kết luận chung

**Chấp nhận** việc sửa trọng tâm:
- Đích là **hai quần thể học được (đèn, xe)** và cách nâng cấp một quần thể mà vẫn phối hợp tốt với các phiên bản đã triển khai của quần thể kia.
- E3/E7 (receiver tín hiệu OLD/NEW) là một kết quả thành công riêng, **không thay** đích xe–đèn.
- Tôi đã để nhánh truyền thông chiếm chỗ đích trong mấy lượt trước. Lỗi đó được ghi nhận ở đây.

## 2. Kiểm từng khẳng định

| Khẳng định của review | Kiểm | Kết quả |
|---|---|---|
| Q7 đã train RL-H, L-ACT, L-RLH, RL-J | `CITY_q7_cross_version.py` (modes `--train-light [--with-fleet]`, `--train-fleet --against`); checkpoint `q7_cross_version_20261002/{RL-H,L-ACT,L-RLH,RL-J}.pt` | ĐÚNG |
| RL-J không phải đồng huấn luyện: chỉ đèn học, fleet bị đóng băng | `train()` dòng ~70: `fleet = load_policy(a.with_fleet)`; chỉ `agent` (đèn) được cập nhật | ĐÚNG. Chưa có pipeline luân phiên/đồng thời — **chưa làm, không phải đã thất bại**. |
| Regression +30,17 / +7,00 / +6,81 / −0,43 | report Q7b | ĐÚNG |
| Cap 50 giữ khoảng 89 % lợi ích, regression 10,89 → 4,05 | frontier: 50: +2,32/+4,05; ∞: +2,61/+10,89 (2,32/2,61 = 0,889) | ĐÚNG |
| Certificate thua tham chiếu đơn giản (0,36 so với 0,40) | B3 | ĐÚNG |
| Có hại ngay trong support (FT) | B4′: mismatch +13,07, K_contract 0 | ĐÚNG |
| Cross-play chỉ ghép cùng chỉ số t | `eval_t*.json`: đèn và fleet luôn cùng t | ĐÚNG — chưa có ma trận chéo seed |
| L-RLH chỉ có ở t = 0 | thư mục q7b không có `L-RLH_t*` | ĐÚNG |
| Đèn được thưởng theo số xe dừng | `LightRL.step`: `R.append(-halt / 10)`, `halt` = `getLastStepHaltingNumber` | ĐÚNG — xem §3, cơ chế còn mạnh hơn review nói |
| Q2: số xe dừng giảm nhưng time loss tăng | C-1 E5: thời gian chờ 11,8 → 9,2 trong khi time loss 30,3 → 45,3 (xe eco theo luật, không học) | ĐÚNG, nhưng là trên xe theo luật; chưa đo trên fleet học |
| CoTV đã huấn luyện chung đèn + CAV | arXiv 2201.13143 / IEEE T-ITS 2023 | ĐÚNG. Ngoài ra còn SGMRL (Stackelberg đèn–xe) nên "cả hai cùng học" và "leader–follower đèn/xe" đều không thể là novelty. |

## 3. Chỗ tôi bổ sung hoặc phản bác

**(a) Cơ chế halting nằm ở cả INPUT của đèn, không chỉ reward.**
- `LightRL.obs` dùng chính `h` = số xe dừng (ngưỡng 0,1 m/s của SUMO) cho mỗi hướng làm 2/7 đặc trưng đầu vào.
- Còn `CarRL.step` phạt `IDLE · [v < 0,1]`. Như vậy fleet học có động cơ bò ở v ≥ 0,1 m/s, tức là **vô hình với cảm biến của đèn**.
- Hệ quả: khi xe được nâng cấp (học), đèn RL-H vốn train với xe người nhìn thấy một input **ngoài phân phối huấn luyện của chính nó** (hàng chờ thật nhưng h nhỏ).
- Đây là bất tương thích **hai chiều**:
  - chiều fleet ← đèn: τ của RL-H nằm ngoài support của L-ACT (OOS 18,6 % ở t0);
  - chiều đèn ← fleet: hàng chờ "ẩn" trong cảm biến của đèn.
- Đây vẫn là giả thuyết, **chưa phải nguyên nhân đã chứng minh**. Kiểm được rẻ bằng checkpoint hiện có (H-crawl, §5).

**(b) "Không thể bê emulator sang" chỉ đúng cho MỘT chiều.**
- Đồng ý cho chiều nâng cấp đèn → xe đã học: pha đèn là vật lý, không thể "emulate" đèn xanh cũ.
- Phần mang sang được ở chiều này là ràng buộc phía người nâng cấp (cap, giữ phân phối pha trong support của fleet) và thông điệp trung thực.
- **Phản bác cho chiều ngược lại** (nâng cấp xe → đèn đã học): đèn là **receiver của dữ liệu cảm biến**. Input cũ ("hàng chờ") là một hàm của trạng thái vật lý. Có thể dựng lại nó một cách **trung thực** từ cảm biến hiện có, ví dụ đếm xe có v < θ với θ khoảng 2 m/s thay vì 0,1. Đây đúng là phiên bản vật lý của legacy-view emulation:
  - không nói dối về đường;
  - không retrain đèn;
  - với xe người thì gần như là phép đồng nhất.
- Vậy E3/E7 có cầu nối thật sang bài toán hai quần thể, nhưng chỉ ở chiều receiver = đèn. Phải kiểm, không mặc định.

**(c) Thứ tự các bước.** Đồng ý 5 bước, với hai điều chỉnh:
- Đưa ablation cảm biến/reward (H-crawl, không cần train) lên cùng bước B (cross-play), vì nó cần để **đọc** ma trận cross-play.
- Đồng huấn luyện (user yêu cầu thử) được làm như **tham chiếu có thêm quyền cập nhật**, cùng ngân sách tương tác, không coi là phương pháp.

**(d) "Fleet gồm receiver cũ/mới đồng nghĩa với hai quần thể xe và đèn" (câu mở của review).** Hiểu là review đang nói về cách tôi đã kể sai. Đồng ý rằng hai thứ **không** đồng nghĩa: E7 có hai *phiên bản* của cùng một vai (đèn tín hiệu nhận packet), còn đích là hai *vai* vật lý khác nhau.

**(e) Novelty (tìm có mục tiêu, không tuyên bố là không có).**

| Đã có | Tài liệu |
|---|---|
| Huấn luyện chung đèn + xe | CoTV; SGMRL (Stackelberg) |
| Thích nghi ego khi partner đổi | FastAP, MEAL / continual MARL |
| Phối hợp với partner chưa gặp | zero-shot coordination, ad hoc teamwork |
| Adapter input cho policy bị đóng băng | MATES |
| Cập nhật MARL có ràng buộc | MACPO, MAPPO-L, Scal-MAPPO-L |
| Robust của TSC theo phân phối nhu cầu / sự cố | — |

- Chưa thấy: **nâng cấp so le** giữa hai quần thể học được, với ràng buộc regression vòng kín lên các fleet đã triển khai, và đo chi phí bảo vệ partner.
- Chưa thấy: bất tương thích **hai chiều** qua cảm biến (fleet học làm mù cảm biến hàng chờ của đèn học).
- Ứng viên novelty khả dĩ nhất: *"staggered-upgrade compatibility between two learned traffic populations"*, gồm
  - ràng buộc phía người nâng cấp: cập nhật đèn có ràng buộc regression với ngân hàng fleet đóng băng;
  - tái dựng input trung thực phía receiver khi receiver là đèn.

  Phải so với: cap, partner-mixture, đồng huấn luyện.
- **Đây chưa phải xác nhận novelty.** W3 các lần dậy phải đọc sâu (method, thí nghiệm, discussion) của CoTV, SGMRL, FastAP, FCP / other-play và MACPO.

## 4. Bảng nhánh (cập nhật, giữ nguyên các nhánh đã thất bại)

| Nhánh | Trạng thái |
|---|---|
| Hại khi nâng cấp đèn | Có thật ở 3/4 cặp; B1 (mọi seed) thất bại — giữ nguyên quyết định hạ cấp |
| Certificate từ log đèn + support | Bị bác (B3) |
| Cap max-green | Frontier có thật; không phải phương pháp mới |
| RL-J (đèn học với fleet đóng băng) | Baseline thật, kết quả không đồng nhất |
| Đồng huấn luyện | **Chưa làm** |
| Cross-play đầy đủ | **Chưa làm** |
| Cập nhật có ràng buộc bảo vệ fleet cũ | **Chưa làm** — chỗ phát triển phương pháp |
| H-crawl (cảm biến/reward halting) | **Mới**; cần ablation |
| V2I / intent / xe mang tin | Tạm gác, không bị bác |

## 5. Kế hoạch cho các lần dậy (theo thứ tự; mỗi bước: protocol → smoke → queue)

- **B0 — kiểm kê.** Thời gian train và eval mỗi run SUMO lấy từ log Q7b, kèm RAM; checkpoint đèn t0–t3 (RL-H, RL-J), fleet t0–t3 (L-ACT, L-FT), L-RLH t0.
- **B1 — cross-play thăm dò.** RL-H_t × L-ACT_t′ (4×4), cộng ACT, cap 50, RL-J_t × L-ACT_t′, trên seed eval 100–104. Ghi:
  - time loss toàn thành phố, approach cost của fleet, người lái;
  - chuyến hoàn thành / dở dang, teleport;
  - **tỉ lệ xe bò** (0,1 ≤ v < 2 m/s trong 200 m).

  Câu hỏi: hại phụ thuộc đèn, xe hay cặp? Có đánh đổi lặp lại được không?
- **B1b — H-crawl.** Đèn đóng băng với cảm biến hàng chờ "crawl-aware" (θ = 2 m/s; hàm đếm mới, không đổi trọng số), trên cùng các cặp. Dự đoán: giảm regression ở các cặp mà tỉ lệ xe bò cao. Cùng lúc tách hai cơ chế: OOS τ phía fleet và mù cảm biến phía đèn.
- **B2 — cặp triển khai đều học (L0, F0).** Train L-RLH_t cho t = 1..3 (fleet huấn luyện với RL-H_t đóng băng), rồi ma trận phiên bản (L0,F0), (L1,F0), (L0,F1), (L1,F1).
- **B3 — đồng huấn luyện (tham chiếu, user yêu cầu).** Luân phiên: k episode đèn rồi k episode xe, lặp lại, cùng tổng ngân sách tương tác với RL-J + L-RLH. Thêm biến thể reward đèn = −time loss (ablation objective, cùng ngân sách).
- **B4 — pilot phương pháp.** Cập nhật đèn với một ngân hàng fleet đóng băng (TRAIN) và các fleet SELECT tách riêng. Các arm:
  - rollback;
  - fine-tune thường;
  - mixture partner;
  - cap tune trên SELECT;
  - cập nhật có ràng buộc regression (Lagrange trên approach cost của fleet);
  - đồng huấn luyện (gắn nhãn là có thêm quyền).

  Không claim phương pháp nếu mixture partner đã đạt cùng trade-off.
- **B5** — chỉ sau khi pilot thắng: seed mới, demand khác, ρ khác, CoTV tái hiện, mạng thứ hai.

Song song (nhiệm vụ còn treo bên E3):
- E9c panel;
- G3 (panel đóng băng đang chạy, script chưa viết);
- G6 (đã chạy);
- E12 (code + run);
- E14 (code + run);
- Lean E12-a;
- tổng hợp E7/E13 vào FRAMING.

Ràng buộc: CPU 10 lõi / RAM 16 GB. SUMO mỗi run 1 tiến trình, nên chạy ≤ 4 lane SUMO cùng các queue E3.

Nguồn văn liệu:
- [CoTV arXiv 2201.13143](https://arxiv.org/abs/2201.13143)
- [CoTV IEEE T-ITS](https://dl.acm.org/doi/abs/10.1109/TITS.2023.3276416)
- [SGMRL, Stackelberg vehicle–signal MARL (IDEAS listing, Physica A 2025 — chưa đọc bản đầy đủ)](https://ideas.repec.org/a/eee/phsmap/v658y2025ics0378437124007994.html); lưu ý: arXiv 2602.23896 là Stackelberg xe–xe (TSC), không phải SGMRL — đã kiểm 01:4x
- [MATES](https://arxiv.org/abs/2609.26010v1)
- [FastAP](https://www.lamda.nju.edu.cn/lilh/file/fastap.pdf)
- [MEAL](https://arxiv.org/pdf/2506.14990)
- [Scal-MAPPO-L, NeurIPS 2024](https://proceedings.neurips.cc/paper_files/paper/2024/hash/fa76985f05e0a25c66528308dda33de0-Abstract-Conference.html)
- [IPPO handshake / heterogeneous teams](https://arxiv.org/html/2512.08877)
- [TSC robustness](https://arxiv.org/pdf/2306.01925)
- [GLOSA ở đèn actuated](https://arxiv.org/pdf/2208.13709)
