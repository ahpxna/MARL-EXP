# MARL: đích, các bước còn lại và điều kiện đóng — 28/09/2026

Independent auditor handoff. Không thay ledger, frozen protocol hoặc producer đang chạy. Đối chiếu với critical path, readiness §8, E3 protocols, code E3 actor/labels/selector/diagnostic/acquisition/delay và draft paper_marl.tex. Đây là audit theo phạm vi đó, không chứng nhận toàn repo hoặc toàn bộ thí nghiệm đã đúng.

## 1. Đích không được tự đổi

Đích người dùng muốn: một bản gửi **paper MARL có bài toán giao tiếp cụ thể, lý thuyết giải thích cơ chế, phương pháp thực thi bằng thông tin hợp lệ, và đánh giá moving traffic trên actor học được với đối thủ đúng**. Không đổi thành “MAPPO thắng max-pressure” rồi coi đó là contribution selector. Không tự đóng thành paper phân tích chỉ vì một lượt negative.

Câu chuyện cần trả lời: commitment vào một order tốn gì; quyền sửa hữu hạn giảm tổn thất nào; vì sao biết có repair tốt không đồng nghĩa học chọn được nó; thông tin trả phí và calibration có giúp chuyển headroom thành team outcome không?

Một method paper không đòi thắng mọi baseline ở mọi điểm, nhưng cần lợi ích thực có thể quy cho thành phần đề xuất dưới resource accounting công bằng: chất lượng, bytes, compute hoặc calibration. Direct là comparator hợp lệ, không phải đối thủ được cố tình hạn chế để R1 thắng. Nếu hết lượt cứu có căn cứ mà chưa có lợi ích, báo scope analysis/empirical study là phương án dự phòng để người dùng/thầy quyết; không tự coi đã đạt đích method.

## 2. Worker đã nắm gì và chưa khép gì

Đã nắm broad scope: có learned MAPPO/CTDE actor, thông tin legal, continuation labels, bid/response ablation, learned SchedNet-style adaptation, E1 và draft. Đã giữ negative results và các claim bị rút.

Chưa khép operational definition of done:
- Status còn các đoạn mâu thuẫn: update đã có actor nhưng section cũ nói actor chưa tồn tại; bảng comparator còn ghi toàn heuristic. Cần một current summary và nhãn historical cho phần cũ.
- “Có đủ comparator” không bằng full original SchedNet: implementation học scheduling trên frozen actor, không học lại message encoder và actor như original. So sánh hợp lệ cho adaptation, không gọi thắng/thua original method.
- Các phép thử mạnh nhất hiện nhiều cái trên scratch s3, chưa là kết luận across independently trained actors.
- Dự trữ seed 1301–1316 không tự tạo một final protocol. Chưa thấy manifest freeze cuối cho actor/selector/comparator/checkpoints/primary endpoint/decision rule.
- Có code mới cho acquisition/delay, nhưng chưa đủ để đánh dấu step 5 hoàn tất.
- T1 traffic bridge chưa đóng; không dùng q90 prediction error làm ε được chứng nhận.

## 3. Các correction đã được làm — không làm lại

MARL_e3_selector_diag_v2.py đã dùng spearmanr với ties, tái tính chọn profile bằng checkpoint và τ, đếm edit bằng chosen index, báo harm/selected gain, và ghi q90 là diagnostic gain error. Kết quả mới: e3_selector_diag_v2_scratch_s3.json. Bản report/draft còn dùng số/cách nói cũ phải cập nhật sau khi đọc v2.

Không suy “safe rule never edits” từ gain khác 0 hay từ mean oracle gain nhỏ hơn threshold. Đếm actual chosen index. Lean SafeEdit có giả thiết pointwise error; dữ liệu quantile chưa đáp ứng giả thiết.

## 4. Công việc bắt buộc tiếp theo, theo thứ tự

### F0 — cập nhật một current scope/claim map, không đợi training

Output một bảng có claim, comparator, object, evidence type, actor seeds, split, source version, trạng thái. Tách:
- actor competence vs MP2;
- message-use ablation;
- selector vs same actor + prefix;
- paid response bid vs no bid và same-byte alternative bid;
- R1 vs direct;
- conditional theory vs actual empirical calibration.

Không chọn actor chỉ vì nó làm method thắng. Nếu G1 gate theo seed, report cả pass rate và toàn bộ actor outcomes; gated subgroup phải ghi là có điều kiện. BC pilot gate và scratch per-seed gate là hai quy tắc khác nhau.

### F1 — hoàn tất dense-label round đã đăng ký, không mở thêm model vô hướng

1. Giữ producer đang chạy, kiểm đủ shard/state, resumed states và checkpoint identity. Resume phải giữ provenance của các phần cũ; source hash lúc kết thúc không tự xác nhận mọi dòng cũ được sinh bởi cùng version.
2. So original và dense trên cùng state intersection trước; báo riêng full dense development panel. Dense t=4..22 tăng snapshot của cùng episodes, không phải số episode độc lập tăng tương ứng.
3. Train/eval variants với cùng tuner/compute allowances. CI resample episode; thêm sensitivity cluster traffic seed khi có hai loads cùng seed.
4. Dùng diagnostic v2: realised selected gain, harm|edit, top-1 regret, pair accuracy excluding true ties, response change precision/recall; không chỉ MSE hay average action accuracy.
5. Chọn threshold phải có option luôn giữ prefix. Khi thêm +infinity, lưu explicit mode/flag: runtime hiện giải None thành -infinity nên không được dùng None cho cả hai. Tạo version mới, không sửa producer đang chạy.

Done: trả lời dữ liệu thêm có cải thiện decision quality hay không. Negative chỉ áp dụng recipe/data scale này, không là theorem không học được.

### F2 — một lượt chẩn đoán/cứu có căn cứ nếu F1 chưa đủ

Không chạy hai chương trình mới rộng cùng lúc.

A. Trên nhãn đã lưu, train diagnostic evaluator biết candidate joint action và prefix joint action (privileged; không deploy). Cùng episode splits/candidate family/target. Nếu nó tốt rõ so với legal evaluator, bottleneck response-information/representation đáng xử lý. Nếu vẫn tệ, chưa có lý do tiếp tục thêm bid.

B. Nếu A ủng hộ: thử một response model dự đoán phase/joint-action distribution, vì head hiện tại chỉ dự đoán có đổi action không. Target có sẵn trong labels; chỉ dùng inputs legal ở deployment. Đánh giá bằng regret của profile chọn, không chỉ response accuracy. Đây là một adaptation có giả thuyết, không phải đảm bảo thành công.

C. Actor hiện train hoàn toàn dưới cached-queue prefix (MARL_e3_actor_train.py:59). Để phân biệt chất lượng scheduler với actor thích nghi theo scheduler, làm một pilot actor train trên mixture cố định giữa prefix và randomized feasible profiles, cùng capacities/byte constraint. Freeze actor và so tất cả selector trên cùng checkpoint. Chỉ nhân nhiều actor seeds nếu pilot đáng tiếp tục.

Nếu deadline không cho C: giữ kết luận hẹp “post-hoc scheduling on prefix-trained actors”, không claim prefix nói chung tốt hơn learned communication. Frozen-actor comparison vẫn có giá trị; nó không đại diện joint actor/scheduler co-training.

### F3 — đóng baseline và byte fairness trước final test

Tối thiểu: same-actor prefix; direct no-bid; direct response-bid; R1 với cùng evaluator/candidates; learned SchedNet-style frozen-actor adaptation; oracle diagnostic riêng. Thêm response-only là mechanism ablation, không cần chạy mọi tổ hợp ở mọi cap.

Thiếu quan trọng: **same-byte queue bid trên learned actor**. Protocol E3 ablation nói fresh queue chưa lưu và định để đến “labelling round of confirmatory test”. Không được dùng final-test labels để train/tune đối thủ này. Thu phần queue cần thiết trên TRAIN/SELECT/DEV trước freeze; hoặc bỏ claim response bid tốt hơn generic fresh summary. Final test chỉ evaluate frozen models.

Giữ cùng absolute total-budget rule, charged control bytes/header/payload và encoding. Nếu cap = own prefix bytes +84 thì different orders có thể khác absolute cap; báo và kiểm fairness theo intended comparison. SchedNet-style hiện có quantized 1-byte execution nhưng float-score stochastic training: ghi training/deploy difference; đây là adaptation, không phải reproduction đầy đủ original.

R1 không cần thắng direct về chất lượng: direct là superset nếu cùng evaluator/search hoàn chỉnh. Lợi của R1 nếu có phải đo ở overhead/calibration/resources; nếu không có thì R1 là ablation/analysis object.

### F4 — acquisition và delay: đã có code, cần khóa cách hiểu/sửa điểm sai

**Acquisition (MARL_e3_acquisition.py):**
- Targeted hiện dùng st['bid'][i]['gap'] đầy đủ. Cái đó không phải thông tin 2-bit gap của bid 1 byte. Nếu claim acquisition chỉ dùng cùng legal bid, dùng bin theo threshold train-only; nếu calibration cho phép privileged features, label là privileged acquisition và cho comparator quyền tương ứng.
- Script wrapper monkey-patch trainer load, nhưng job source_hashes của trainer không tự include wrapper/strategy/B. Lưu riêng wrapper hash, B, strategy, subsample seeds và actual per-state chosen masks.
- size=min(B,len(pool)) có thể làm số query khác B; assert pool đủ hoặc report actual costs và match budget. Không mặc định same B trong CLI là matched measured cost.
- Select/dev full label tables là overhead chung. Report training acquisitions riêng và total labelling cost; không gọi 24/total candidates là toàn bộ chi phí hệ thống.
- Sinh lựa chọn bằng permissible metadata trước khi đọc candidate cont/joint labels. Đây là offline replay of an acquisition rule, không tự là adaptive online acquisition.
- Bản targeted “near tie” không tự có A starvation hoặc B obstruction-order guarantee. Nếu không hơn uniform thì giữ negative, không cố gán novelty.

**Delay (MARL_e3_delay.py):**
- Hiện tác động actor bằng lịch sử receiver cache bị trễ, còn scheduler/env mirror/cache truyền vẫn hoạt động zero-delay. Chỉ chạy prefix R0 và MP2/learned actor.
- Vì vậy kết quả là delayed receiver-observation stress test với scheduler idealized; chưa phải full bid→select→payload network-delay test của phương pháp.
- Chọn một trong hai scope trước viết: (i) giữ stress test và nói đúng, không claim robustness phương pháp với network latency; (ii) nếu giữ claim đó, thêm delivery queue/bid age và selector dưới cùng delay, delay ảnh hưởng cả legal information/mirror. Không bắt xây packet-loss/jitter model nếu không claim.
- d=0 identity self-check kiểm equivalence ở zero, chưa kiểm packet causality khi d>0. Thêm timestamp assertion tương ứng scope nếu viết network-delay semantics.

### F5 — một bridge panel nếu muốn giữ headline theory-guided

T1 là conditional theorem cho same score/top-prefix và global marginal bound. Chọn một reduced receiver–sender subproblem có thể duyệt đủ trên một frozen actor, giữ phần còn lại cố định. Đo các optimum với/không radius, có/không byte cap, và candidate restriction; kiểm η trên toàn không gian nhỏ ấy, không one-swaps. Tách oracle geometry/evaluator error/coverage loss.

Done: ít nhất biết bound có explanatory power hay rất lỏng cho một actor-realized object. Certificate chỉ trong reduced problem. Nếu không làm, ghi theory–traffic instantiation còn mở và hạ headline “theory-guided guarantee”; không coi gate Lean đã thay bridge.

Không cần prove generic MARL convergence, toàn bộ neural drift hoặc exact whole-network η trước nộp.

### F6 — final protocol + freeze trước mở 1301–1316

Lưu một immutable final protocol/manifest:
1. Recipe actor nào, tất cả actor seeds nào, cách xử lý G1 fail, checkpoints và hashes.
2. Model/threshold/candidate generator/normalization/bid bins/byte encoding của mọi method.
3. Comparator chính và primary endpoint: ví dụ paired relative episode waiting với cùng actor; thêm throughput/unfinished guardrail; practical effect size target do tác giả chốt trước test.
4. Ba hoặc bốn fixed absolute cost points nếu claim frontier; không dùng cùng một test để chọn cap thắng rồi gọi confirmatory.
5. Evaluation traffic/capacity seeds và một shift; không cần một simulator khác.
6. Aggregation theo actor training seeds và traffic episodes, không coi selector initializations là actor replications. Report individual actor seeds và paired uncertainty.
7. Negative interpretation: CI chứa 0 nghĩa là chưa chứng minh improvement, không chứng minh equivalence. Nếu muốn claim no meaningful benefit, chốt equivalence/non-inferiority margin trước.
8. All endpoints, failures, censoring, retries và no-oracle-access checks.

Chạy một lần theo freeze. Nếu sửa code/method sau khi xem test, panel đó thành development cho phiên bản mới; không gọi lại là untouched confirmation.

### F7 — manuscript/release làm song song, không đợi test mới viết

Draft đã có nhưng không phải chỉ còn 8 TODO:
- Methodology hiện vẫn mô tả 3-class MP2 response model và held-phase target. Learned-actor branch dùng binary change head và continuation. Viết thành hai stages/recipes rõ ràng hoặc rewrite around final method.
- Limitations còn câu “Fixed MP2 actor in every traffic result”; sai sau E3. Cập nhật toàn section, không chỉ thêm paragraph kết quả.
- Related work thiếu các neighbors đã research: NDQ, CASEC, M2I2 (AAAI 2026), MUTE (preprint), và precise distinction với Dense Coverage. Không claim action relevance/joint-action prediction/Top-k across budgets là mới.
- Tách actor improvement và selector increment trên figures. Không dùng MP2 làm comparator duy nhất cho proposed selector.
- Status/claim map chỉ giữ một current truth; phần cũ archive/label historical.
- SafeEdit gate chỉ chặn nhãn formal cho theorem đó; không chặn empirical runs.
- Bốn hình: protocol/action example; controlled geometry/calibration; learned-actor quality-vs-total-bytes; failure/response/acquisition decomposition. Nếu delay chỉ actor stress test, đưa supplement/table.
- Exact source/config/checkpoint manifests; reproducible small command; compile source và visual-check PDF; anonymity theo track.
- Venue/track/deadline do tác giả/thầy xác nhận. Chưa xác nhận không chặn hoàn thiện nội dung và experiments.

## 5. Điều kiện đóng bản gửi

Method scope: learned actor hợp lệ; selector có incremental benefit được đánh giá đúng comparator/resources hoặc tradeoff hữu dụng khác; explanation không tách khỏi actual algorithm; frozen main experiment và limitations; manuscript/repro ready.

Nếu incremental benefit chưa có: báo rõ điều kiện method scope chưa đạt. Một analysis+empirical-limits submission vẫn là MARL nghiên cứu, nhưng đây là thay scope tác giả phải chấp thuận, không tự ghi xong.

Những việc không cần chen vào đường găng: simulator mới, thêm 10 theorem, full arbitrary-channel calibration, chứng minh nesting-degree equality, train lại A/B/C, mở nhiều architectures cùng lúc. Full gate đã pass không cần lặp lại chỉ vì sửa prose.

## 6. Thứ tự bàn giao ngắn

Ngay: current claim map → diagnostic v2 vào report → dense round → targeted cause diagnostic/adaptation nếu cần.
Trong lúc chờ: sửa acquisition legality/provenance, chốt delay scope, thu TRAIN/SELECT data cho same-byte baseline, rewrite Methodology/Limitations/related work.
Sau development: freeze actor+selector+baseline+endpoint → fresh test 1301–1316 → finalize figures/conclusions/PDF/artifact.

Đây là hướng dẫn thực thi; không tự chạy thêm heavy jobs, không gửi message cho worker và không đổi framing thay người dùng.
