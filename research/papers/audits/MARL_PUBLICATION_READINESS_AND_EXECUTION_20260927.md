# Audit toàn tiến độ MARL và đường tới bản gửi CCSC Eastern — 27/09/2026

Bản độc lập để giao worker. Root: /Users/phanan/cig-amf-main. Không sửa ledger, protocol đang chạy hoặc producer lịch sử. Không khởi chạy training/rollout mới. Các con số mới dưới đây được tính lại từ rows/episode, không lấy nguyên bảng báo cáo. Trạng thái là ảnh chụp cuối ngày 27/09; B4 còn chạy khi kiểm.

## 1. Kết luận và phạm vi

**Chưa hoàn thành một paper phương pháp MARL. Đã có một bộ lý thuyết, controlled experiments, hạ tầng giao thông và một kết quả held-phase dương có giá trị.** Không có bằng chứng buộc phải bỏ CityFlow. Cũng chưa có bằng chứng cho headline “bounded repair cải thiện MARL trong closed loop”.

Điểm nghẽn hiện tại gồm:
1. Actor vẫn là MP2 cố định, chưa phải actor học bằng RL.
2. B2 dương ở held-phase; B3 và panel closed-loop mới chưa xác nhận cải thiện.
3. Thành phần được dữ liệu ủng hộ là **bid trả phí + direct selector**, trong khi phần toán nổi bật là **priority + bounded revision**. Hai nửa chưa ghép thành cùng một contribution thực nghiệm.
4. Một số giả thiết của toán chưa khớp protocol: global ScoreLocal, top-score prefix, coupled byte cap, thông tin riêng của actor.
5. Chưa có manuscript MARL trong research/papers/_tex.

Không báo “80%/90%” vì khối chưa xong là bằng chứng trung tâm, không phải việc trình bày. Gate không còn là đường găng.

Đã đọc các critical-path/scope/result documents và nội dung producer, selector, transport, labeler, trainer, runtime, module Lean liên quan; đối chiếu B1/B2/B3/B5/B6, E1, gate và các artifact mới. Đợt này đi sâu vào MARL hiện hành, không phải chứng nhận lại mọi file của 7 paper cũ và A/B/C. Các phát hiện E1/B1 đã có audit riêng được giữ nguyên, không giả vờ đọc lại toàn corpus.

Các điểm vào quan trọng đã kiểm:
- research/papers/audits/MARL_SUBMISSION_CRITICAL_PATH_20260927.md
- research/papers/audits/MARL_CRITICAL_PATH_STATUS_20260927.md, kể cả bản vừa cập nhật; bản cũ trong legacy.
- research/marl_budget/BASELINES_DIRECT_STAGEA2_RESULTS_20260927.md
- scripts/MARL_hetero_pilot_collect.py, MARL_hetero_onpolicy_collect.py
- scripts/MARL_hetero_closed_loop.py, các bản v2/v3/v4
- scripts/MARL_hetero_direct_indep_dev.py, MARL_hetero_top2_joint_v2_dev.py
- scripts/MARL_hetero_eta_bridge.py, MARL_make_fig3_v3.py
- models/marl_hetero_selector.py; envs/external/cityflow_hetero.py và mirror/access interfaces
- LeanMarlEstimatedRevisionV1, RevisionAuditBridgeV1, ProfileSearchV1, BlockFrontierV1, NestingDegreeGeneralV1, E1bRealizationV1; các audit trước đã đối chiếu T2/CalibrationGap/PairCalibration.
- Hạ tầng cũ models/policy_value.py, scripts/run_external_training.py: có thứ tái dùng, chưa phải learner của protocol hiện hành.

## 2. CCSC Eastern: phải phân biệt “trình bày” và “publication”

Nguồn chính thức đọc ngày 27/09:
- Faculty paper: https://sites.google.com/site/ccsceastern/participation/papers/authors
- Deadline: https://sites.google.com/site/ccsceastern/participation
- Student paper: https://sites.google.com/site/ccsceastern/participation/studentpapers

Faculty track có phản biện ẩn danh; bài được nhận và trình bày được đưa vào JCSC. Trang hướng dẫn hiện quy định tối đa **15 trang gồm tài liệu tham khảo**, dùng CCSC LaTeX template. Student paper có committee review nhưng không xuất bản toàn bài trong journal; trang dành cho doctoral students cũng nói muốn peer-reviewed publication thì nộp faculty track.

Website ghi faculty deadline 31/05/2026, student 30/06/2026 và có thể nhận muộn; các track khác ghi 15/09. Không mặc định còn cửa nộp faculty 2026. Cần xác nhận với thầy: track nào, năm nào, có deadline/ngoại lệ được ban tổ chức chấp thuận không. Đây là xác minh đích nộp, không ngăn việc hoàn thiện bản thảo.

Không lấy checklist kiểu hội nghị ML lớn làm quy định bắt buộc của CCSC. Một nghiên cứu tập trung, tái lập được, so sánh đúng và giải thích rõ có ích hơn việc nhồi tất cả theorem và simulator. Nhưng đổi venue không biến fixed MP2 thành learned MARL.

## 3. Trạng thái thực tế, kể cả tiến triển ngoài báo cáo cũ

| Hạng mục | Bằng chứng hiện có | Còn thiếu/giới hạn |
|---|---|---|
| T1 + feasibility + profile search | Module và smoke gate PASS | Chưa tự động áp được toàn bộ bound cho protocol có byte cap và learned traffic |
| T2 needle/fixed schedule/pair | Đã compile/gate; fixed-schedule log-cardinality gap đã xử lý | Không gọi adaptive bound matching mọi tham số; pair tightness còn mở |
| E1a | Kênh controlled khớp T2 | Giữ scope Gaussian needle |
| E1b | Actor Bayes chạy được, mean-value realization, crossover của chiến lược | Không phải kênh Gaussian pair của T2; không có generic “R lớn bắt buộc học khó hơn” |
| B1 | Learning curve đã FAIL theo đăng ký | Chứng cứ về các learner đã thử, không phải bất khả thi thông tin nói chung |
| B2 | Confirmatory held-phase PASS, chênh +1.85, CI [0.95,2.84] so control | Direct selector + bid trả phí; không phải R1 thắng direct, không phải traffic return dài hạn |
| B3 | Closed-loop FAIL | −0.26% waiting vs control; CI chứa 0 |
| Panel mới 1101–1116 | COMPLETE, 32 episode; tính lại raw rows | Cũng không xác nhận closed-loop gain |
| B5 | FAIL, Δ≈1.02, CI [−0.04,2.13] | Không đổi “sát ngưỡng” thành PASS |
| B6 | Có kết quả held-phase theo load/capacity | Không robust ở fixed/bursty/low; chưa phải closed-loop robustness |
| B4 | On-policy labels và top2 models đã xong; controls đang train | Chưa có verdict closed-loop 801–816 tại snapshot audit |
| Stage A v2 | COMPLETE ở dev | Cải thiện nhỏ; 27 inputs, runtime cũ 23 inputs; chưa deploy |
| Direct train riêng | Cả ctrl và top2 COMPLETE, 3 init seeds mỗi loại | Dev đã mở; chưa đánh giá closed-loop độc lập cho checkpoint mới |
| Baseline request v4 | COMPLETE; leak exact-gap đã sửa | Heuristic, không phải Where2comm đã train |
| Latency B2 | median scheduler≈16.6 ms, p95≈17.9 ms | Compute only, không gồm uplink/network; chưa có latency cho mọi baseline |
| Learned actor | Chưa có trong pipeline này | Việc trung tâm nếu giữ claim MARL phương pháp |
| Manuscript | Chưa có MARL .tex | Có thể viết protocol/method/theory ngay, không chờ mọi experiment |

SmokeMARL17, smokeMARL4 và smokeMARL1_E1b đều PASS theo các SUMMARY đã kiểm. Không cần chạy lại toàn gate chỉ vì đang audit hoặc vì chưa viết manuscript.

### Panel closed-loop mới: tính độc lập từ rows

Nguồn:
- research/marl_budget/cl_baselines_20260927_232931
- research/marl_budget/cl_w2c_bin_20260927_234219

32 episode = 16 traffic seeds × 2 loads. Trung bình init seeds trong mỗi episode trước; bootstrap paired episode 10,000 lần. Kiểm thêm bootstrap theo 16 seed clusters, gộp hai load trong seed, như sensitivity analysis. CI có thể khác rất nhẹ bảng worker do RNG bootstrap; không thay endpoint cũ.

| Phương pháp | Thay đổi waiting so prefix, % [95% CI] | Bytes/decision |
|---|---:|---:|
| Prefix | 0 | 188.20 |
| Control direct không bid | +0.175 [−0.313, +0.738] | 190.33 |
| B2 direct + top2 bid | −0.281 [−1.659, +1.143] | 201.89 |
| Fresh-queue heuristic | +4.699 [+2.028, +7.364] | 199.11 |
| Request heuristic v4, đúng bid | +0.526 [−1.405, +2.525] | 234.80 |
| Held-phase oracle reference | −14.373 [−16.687, −11.990] | 221.43 |

Negative waiting change là tốt. **B2 vs control = −0.467%, CI [−1.649,+0.707]**. Không có bằng chứng thắng ở endpoint này. Oracle là một policy privileged dùng held-phase search, không phải chứng nhận optimum của toàn MDP.

Đã kiểm: mọi method đủ episode; learned/control có đủ 3 init; prefix v4 trùng v3 cả queue, finished, bytes ở 32/32 episode; listed producer hashes khớp; deployable oracle flags đều false. Kiểm flags không chứng minh mọi loại leak đều vắng mặt: leak precision ở v3 là ví dụ.

Script audit độc lập:
research/papers/audits/MARL_PUBLICATION_AUDIT_RECALC_20260927.py

Bảng số, source hashes, episode/seed-cluster CI:
research/papers/audits/MARL_PUBLICATION_AUDIT_NUMBERS_20260927.json

## 4. Những điểm đúng/sai còn cần xử lý

### 4.1 Đã sửa: exact-gap leak và nhãn baseline

v3 dòng 59–70 lấy gap thực rồi xếp receiver theo gap; bid chỉ truyền gapbin 2 bit. v4 dùng (gapbin, receiver ID); tôi đã đọc code và kiểm lại artifact mới. Đánh dấu **resolved cho v4**; giữ v3 lịch sử có nhãn.

Fresh-queue và request là heuristic. Không được viết “beats SchedNet/Where2comm”. SchedNet thật học scheduling, encoding và action; Where2comm là cooperative perception bằng confidence maps. Tên baseline trong figure phải mô tả bản thực thi.

### 4.2 Đã sửa ở report, chưa được biến thành theorem: η

MARL_hetero_eta_bridge.py:25–35, 64–75 chỉ fit one-swap quanh prefix. η suy ra là LOWER bound của global ScoreLocal constant. Không dùng nó làm UPPER certificate.

Bản status mới đã rút claim. File JSON lịch sử vẫn có tên frac_zero_price_certified; downstream table/figure phải dùng nhãn đã sửa. Không bắt buộc rerun rollout. Counterexample f(S)=1[{2,3}⊆S], P={0,1}, k=2: mọi one-swap gain=0 nhưng đổi cả hai gain=1.

### 4.3 Mới cần sửa: nesting degree chưa có đẳng thức

LeanMarlNestingDegreeGeneralV1.lean:19–34 ghi rõ lower bound và matching upper là conjecture. Có:
R*(m) ≥ floor((m+1)/4)
theo construction đã phát biểu, không có theorem equality tổng quát. distance_regret_lower xử lý optimum duy nhất hợp lệ; không cần lặp lại phản đối “chỉ chọn một optimum xấu”.

**Việc làm:** trong novelty table/manuscript ghi linear lower bound + finite-size evidence, hoặc bỏ exact formula khỏi headline. Không trì hoãn bản gửi để giải matching upper.

### 4.4 Mới cần làm rõ: “nesting forced” không đúng vô điều kiện với transport hiện tại

models/marl_hetero_selector.py:38–50 cho phép chọn mô tả rẻ hơn giữa patch và explicit profile. envs/external/cityflow_hetero.py:56–77 broadcast union, cập nhật đúng các S_i; nó không mô phỏng receiver nghe một prefix thời gian rồi ngắt.

Vì vậy:
- R0 là common-order baseline/commitment model;
- receiver capacity hiện là **số payload được decode**, không phải thời lượng nghe luồng;
- explicit profile được phép, nên direct selection là đối thủ hợp lệ; nesting không bị phần cứng cưỡng bức trong toàn policy class này.

**Cách sửa ít tốn công:** mô tả chính xác “shared broadcast with heterogeneous decoding budgets and optional profile instructions”. Giữ bài toán committed-order trong lý thuyết, dùng explicit direct để đo cái giá của commitment. Không cần viết simulator mạng mới. Nếu muốn claim interruption/physical prefix delivery thì phải có thêm transport model, không chỉ đổi câu chữ.

Cardinality hiện là |S_i|=K_i, không phải ≤K_i. Với fixed actor nonmonotone, thông tin thêm có thể làm xấu; không mặc định full communication là upper bound. Ghi “exact-cardinality profile” trong method, hoặc triển khai quyền bỏ qua với matched baselines ở phiên bản sau.

### 4.5 Mới: T1 chưa trả hết giá của byte feasibility

BlockFrontier yêu cầu prefix top-score trong từng block và ScoreLocal trên các tập liên quan. Runtime chọn cached-queue order, không có chứng minh nó top-score của cùng vector dùng trong fit η. Hơn nữa bound theo R không tự trả coupled cost của union payload/control.

Đừng sửa bằng cách thêm giả thiết không kiểm rồi gọi bridge đã đóng. Có decomposition minh bạch ở §5 dưới. Cái gì chưa có analytic bound thì giữ là term cần đo, không tuyên bố bằng 0.

### 4.6 B3 “do covariate shift” đang mạnh hơn bằng chứng

On-policy B4 sửa state distribution, nhưng Labeler vẫn gọi oracle_rollout_value với joint action giữ cố định, H=3. Khi chạy live, những bước sau lại sense/select/act. Đây còn là **khác biệt target** giữa held-phase score và continuation return.

Parity trên vài snapshot loại được một số wiring errors; nó không chứng minh nguyên nhân duy nhất là covariate shift. Viết “consistent with distribution shift; held-phase target mismatch remains another hypothesis”.

Nếu B4 âm, không mở B7–B20 mò features. Làm một diagnostic cố định nhỏ: tại cùng development states, so xếp hạng của held-phase labels với labels “first action from S, then a declared common closed-loop continuation”. Dùng cùng simulator randomness, cùng H, giữ actor cố định; báo top-choice disagreement và thực gain, không chỉ correlation.

### 4.7 Direct độc lập là tiến triển thật, nhưng còn giới hạn

Direct wrapper chọn epoch theo direct +84 thay vì R1 +28; tôi đã kiểm logic. Hai run đã COMPLETE. Đây vẫn là cùng họ critic regression + candidate argmax, không phải một architecture sinh subset hoàn toàn khác.

Development cho direct hơn R1 tại một số cap; đó là lý do rút claim repair superiority, không phải lý do loại direct khỏi bài. Muốn claim ít revision vẫn đáng dùng, phải đo cùng bytes/compute và chứng minh một trade-off thực, không chỉ vì theorem có R.

### 4.8 Provenance và latency: đừng nâng chứng cứ

PROVENANCE_SUPPLEMENT lưu wrapper hashes sau run cùng mtime trước launch. Điều này hỗ trợ provenance nhưng **mtime không chứng minh tuyệt đối file không từng thay đổi**. Ghi “retrospective supplement”, không gọi bằng prospective source freeze. Đợt cuối freeze cả dependency closure, wrappers, coefficient JSON, config, data/model hashes.

CPU contention có thể tăng latency; chưa có phép đo paired idle-vs-busy thì không khẳng định mức bias đã biết. 0% misses ở 50 ms trên sample chỉ là observed compute result. Không claim end-to-end deadline khi environment có zero network delay.

Figure 3 tại một cap là comparison of operating points; chưa phải một Pareto frontier nhiều budget. Latency chỉ hai method thì ghi rõ, không suy runtime ranking toàn bộ.

## 5. Mắt nối toán–method nên viết, không cần mở một chương trình Lean mới

Đặt X là trạng thái thật, Z là thông tin hợp lệ, K là capacities, S là profile. Với actor π và continuation c đã khóa:
f_X^{π,c}(S) = E[return | X, first profile S, continuation c].
Nếu label giữ phase H bước thì c phải được ghi đúng là hold, không ghi đó là Q của policy live.

Learner công khai có thể học
fbar_z(S) = E[f_X(S) | Z=z, K],
không mặc nhiên biết f_X(S). Trên cùng feasible family biết từ Z,K:
E[max_S f_X(S) | Z,K] − fbar_Z(S_hat)
= {E[max_S f_X(S) | Z,K] − max_S fbar_Z(S)}
  + {max_S fbar_Z(S) − fbar_Z(S_hat)}.

Hạng đầu là giá của thông tin bị thiếu so với privileged oracle; hạng sau là regret chọn của learner. Oracle joint-action gap không tự bằng phần gain có thể thu bằng một byte.

Tiếp theo, với value f cố định, đặt:
- F_all: mọi profile đủ cardinality;
- F_R: profile cách prefix không quá R ở mỗi receiver;
- F_R,B: F_R và byte cost ≤ B;
- C ⊆ F_R,B: candidates thực sự được chấm;
- V_D = max_{S∈D} f(S), với các tập không rỗng.

Khi output nằm trong C:
V_all − f(S_hat)
= (V_all−V_R) + (V_R−V_R,B) + (V_R,B−V_C) + (V_C−f(S_hat)).

Tên các term:
1. geometric/commitment loss;
2. byte-feasibility loss Δ_byte;
3. candidate-coverage loss ζ;
4. estimation/search loss.

Nếu |fhat−f|≤ε trên C và optimizer cách max_C fhat không quá ν, term cuối ≤2ε+ν. Chứng minh: lấy maximizer f trên C, cộng trừ fhat ở nó và ở output, mỗi sai số ≤ε. Đây là argmax stability cơ bản, không phải novelty tự thân.

Chỉ khi các giả thiết hTop và ScoreLocal của BlockFrontier đã thỏa, term đầu mới được chặn bởi 2η Σ_i(d_i−R)_+. Nếu không, để nguyên term đó; đừng lắp η one-swap vào.

Bid B_bid làm feasible budget còn B−B_bid và bổ sung Z. Đây là đánh đổi information vs payload, không có định lý “thêm bid luôn tốt”. Thực nghiệm phải giữ total budget, tính luôn bid kể cả khi chọn prefix.

Bản decomposition trên là hand derivation của audit; chưa là module Lean mới. Viết thành proposition ngắn đủ phục vụ manuscript; formalize sau nếu cần theo quy trình repo, không để nó cản actor.

Một cải thiện toán nhỏ tùy chọn cho E1b:
marginal = g_i² + β² I với I∈{0,1}, nên dùng w_i=g_i²+β²/2 cho **mọi i** cho ScoreLocal constant β²/2. Uniform shift giữ nguyên ranking và không cần biết interacting pair. Proof chỉ tách I=0/1. Module hiện dùng pair-dependent shift; không nên dùng shift đó như learned score biết pair miễn phí. Cải thiện này không formalize observation law và không tạo guarantee traffic.

## 6. Câu chuyện sắc nhất hiện giờ

Câu hỏi nên giữ:
**Khi các receiver có budget khác nhau, chất lượng phối hợp mất vì commitment, vì giới hạn repair, hay vì scheduler không biết actor sẽ phản ứng ra sao; một bid nhỏ trả phí mua lại được gì?**

Chuỗi bài:
1. Một priority phục vụ nhiều receiver/budget, nhưng joint value có interaction.
2. T1 tách geometric floor khỏi lỗi học/search; thêm byte feasibility và thông tin hợp lệ.
3. T2 minh họa chi phí calibration của ambiguous repairs trong class cụ thể.
4. CityFlow đo đúng ba thành phần: oracle headroom, learner access, và closed-loop transfer.
5. Method dùng local response bids và evaluator để lựa chọn; R là một knob cần đánh giá, không được mặc định R1 là winner.

Câu chuyện **hữu ích** vì nó phân biệt quyền sửa với khả năng biết sửa thế nào. Nó chưa hoàn chỉnh thành “method cải thiện MARL” vì actor và closed-loop evidence còn thiếu. Không thay câu hỏi bằng “train một MLP tốt hơn” rồi giữ nguyên novelty toán trong abstract.

Asset được giữ:
- C → committed order, aware comparator, revision geometry; không mang fairness/parity sang traffic khi không có ràng buộc tương ứng.
- A → phân biệt proxy/true value và calibration allocation. Hiện không claim every/near-optimal starvation trong traffic nếu chưa nối optimizer với mass bound.
- B → acceptable repair và information needed to choose; T2 là restricted instantiation, không phải safe-driving exponent theorem.
- 7 paper cũ → actor/training/adapter/metric infrastructure và context. Không cần nhét cả 7 contribution vào một bản 15 trang.

### Novelty cần viết hẹp

Nguồn gần, đã kiểm lại:
- SchedNet: https://arxiv.org/abs/1902.01554 — scheduling/encoded messages/actions đã được học dưới shared bandwidth. “Learn who talks” và fresh importance bids không phải novelty.
- Where2comm: https://proceedings.neurips.cc/paper_files/paper/2022/hash/1f5c5cd01b864d53cc5fa0a3472e152e-Abstract-Conference.html — confidence-based cooperative perception; không phải tên hợp lệ cho heuristic traffic hiện tại.
- Dense Coverage, Sparse Refinement: https://arxiv.org/html/2609.29456 — nested top-N theo additive selection surrogate. Bài có contextual attention và nonlinear fusion; không mô tả họ “không xét tương tác” theo nghĩa toàn hệ thống. Đối chiếu đúng phần scalar-score selector.
- Incremental Submodular Maximization: https://arxiv.org/abs/2606.28558 — một ordering cho mọi cardinality đã có literature.

Candidate contribution còn bảo vệ được: **interaction-dependent quantitative cost of committed priorities and bounded revision, separated from the data/information needed to choose useful revisions**, với một protocol cụ thể và empirical audit của applicability. Không bảo đảm “không collision với bất kỳ bài nào”; không cho điểm novelty thập phân. Auxiliary action prediction, finite argmax stability và DAgger là machinery có sẵn. Nếu method cuối chỉ direct+bids thì phải giải thích đóng góp ngoài việc ghép machinery đó, bằng câu hỏi/cơ chế/ablation nêu trên.

## 7. Đường găng cụ thể giao worker

### P0 — trong lúc B4 chạy: sửa phạm vi, bắt đầu viết

1. Giữ B4 protocol/checkpoints/producer đang chạy nguyên trạng. Theo dõi COMPLETE, đủ methods và seeds; không chọn checkpoint bằng test.
2. Sửa narrative còn “nesting forced” theo §4.4; exact nesting degree → lower bound.
3. Cập nhật claim table 8–12 hàng: claim, theorem/assumptions, code, artifact, empirical/theorem status. Không cần thêm ledger thứ năm.
4. Tạo research/papers/_tex/paper_marl.tex theo template venue sau khi xác nhận track. Viết problem/protocol/method/known theorem/experiment design ngay. Results chưa có ghi rõ TBD trong working draft, không bịa số.
5. Fig3 dùng v4 đã sửa. Ghi “fixed MP2” và “accounted bytes, zero delivery delay”. Không gọi closed-loop curves là learned MARL.
6. Caption E1 tiếp tục phân biệt theorem-aligned E1a với Bayes mean-model E1b. Targeted≡uniform là negative control, không phải acquisition thắng.

Done: bản có thể cho thầy đọc về câu hỏi, model, contributions, limitations; không chờ chạy hết mọi thứ mới bắt đầu viết.

### P1 — đóng B4 và quyết định đúng cái nó đo

1. Chờ controls và closed-loop dev/test kết thúc; kiểm train/select/test separation, nguồn, checkpoint.
2. Tính endpoint đã đăng ký: waiting vs control, mean vs prefix, finished difference. Báo init seeds riêng và episode/traffic-seed uncertainty.
3. Đừng thay direct thành R1 hay Stage A v2 sau khi thấy 801–816. Nếu đổi thì kết quả cũ vẫn giữ, bản mới là development hoặc cần validation mới.
4. PASS → có evidence cho selector trên fixed MP2; tiếp tục actor pilot.
5. FAIL → nói rõ on-policy update chưa đủ. Làm duy nhất diagnostic target/continuation ở §4.6 nếu cần quyết định sửa nhãn. Nó không chứng minh CityFlow/MARL không thể làm được. Không mở thêm features vô hạn.
6. Direct checkpoints vừa train riêng chưa có closed-loop verdict: đánh giá chúng như comparator đúng scope, không lấy dev CI làm confirmation.

Done: một verdict ngắn, kiểm được; B4 không bị gọi nhầm là actor training.

### P2 — xây actor MARL tối thiểu và kiểm communication thực sự hữu ích

Sau verdict B4, đây là bước tới mục tiêu người dùng đã chọn; không cần chờ theorem mới.

1. Reuse models/policy_value.py và training machinery cũ có chọn lọc. Viết một input adapter duy nhất từ own view + received mask/payload + age/cache. Zero missing và missing indicator phải khác nhau.
2. Nếu CTDE, critic được privileged state khi train; actor/selectors runtime chỉ nhận declared view. Đừng reuse full-neighbour observation của runner cũ như thể nó bị budget mask.
3. Chọn một algorithm sẵn có làm backbone; không đồng thời phát minh optimizer mới. Train một seed smoke với random budgets/masks đã khóa, lưu schema/checkpoint/seed/config.
4. Kiểm message-use: full/no/stale/shuffle communication trên cùng actor; mục tiêu xác nhận channel tác động policy, không buộc full phải luôn thắng. Kiểm masked payload không đọc được bởi actor.
5. Port bid: actor tự tính top-2 action IDs và quantized gap từ own legal input. Bỏ MP2 coefficients khỏi inference nếu actor không còn MP2. Học response model bằng executed/counterfactual actor labels trong train only.
6. Calibrate evaluator lại theo actor này, không dùng value labels MP2. Freeze actor trong mỗi selector comparison.
7. Mọi update actor → checkpoint/version mới, calibration refresh; không cần neural drift theorem tổng quát.
8. Một seed chỉ là wiring pilot. Nếu có học/communication signal và runtime hợp lệ mới mở main training. Không kết luận thắng từ một seed.

Done: một checkpoint actor được train bằng team objective, action thay đổi hợp lệ theo message, evaluator cùng actor/continuation; đây là điều hiện chưa có.

### P3 — gói experiment tối thiểu, tránh fan-out

Main panel trên một topology CityFlow là đủ cho scope hẹp. Giữ held-out loads; không bắt làm thêm CARLA/Minecraft/4×4 ngay.

Các hàng so sánh tối thiểu:
- no/full communication reference;
- cached-score prefix;
- learned scheduling baseline theo SchedNet principles, adaptation được mô tả đầy đủ;
- direct selector được train/tune riêng, cùng actor, context và byte budget;
- method response-bid với R=0, R=1, direct; R=2 chỉ nếu còn câu hỏi rõ;
- oracle nhỏ làm reference, ghi restricted candidate nếu không exhaustive.

Không cần train lại toàn bộ perception backbone Where2comm trên traffic-control task chỉ để có một tên nổi tiếng. Một request/confidence baseline đúng nhiệm vụ là đủ nếu ghi adaptation/heuristic chính xác. Không claim outperform original Where2comm.

Các trục ablation, dùng chung data/model để tiết kiệm:
- cùng bid nhưng bỏ response head;
- cùng head nhưng không bid;
- queue bid và response bid cùng số byte;
- R1 vs direct cùng evaluator và compute/candidate budget, rồi thêm direct tune riêng;
- prefix-trajectory labels vs B4-style labels chỉ khi đây là claimed ingredient.

Main metric:
- cumulative waiting (define sampling interval);
- finished/unfinished và throughput;
- travel time đi cùng censoring/unfinished, tránh chỉ chọn xe hoàn thành;
- **total** bytes = bid + payload + control;
- total scheduler compute; pre/post grant riêng nếu có ý nghĩa.

Chốt trước primary comparison và operating point. Khởi đầu tối thiểu 3 independent actor-training seeds để thấy variance; 5 nếu khả thi và cần cho claim. Đây là khuyến nghị thiết kế, không phải quy định venue. Init seeds của selector không thay actor seeds. Paired traffic/budget seeds; báo tất cả, không chọn seed thắng.

Muốn performance–bytes curve: chốt ít nhất 3 total budget points trên cùng design, không ghép method khác cap rồi gọi dominance. Cap “prefix bytes +84” có baseline phụ thuộc state/order; báo absolute charged bytes và kiểm fairness thay vì mặc định mọi phương pháp dùng đúng cùng bytes.

Một distribution shift đủ để có câu chuyện giới hạn; không đòi thắng cả fixed/bursty/low. Nếu không bền thì report limitation, không xóa panel.

Muốn claim network-latency/real-time: thêm declared bid/uplink/payload delay và cho nó tác động clock/observations của simulator. Nếu deadline không đủ, **bỏ claim end-to-end**, giữ compute-only measurement và zero-delay application scope. Không bắt xây network simulator để chỉ nộp một method study.

Done: method có bằng chứng đúng claim trên learned actor, các comparator không yếu do tuning bất cân xứng, đủ cost accounting và uncertainty. Nếu không thắng, không sửa protocol để ép kết quả; chọn headline empirical boundary cho đúng bằng chứng.

### P4 — bốn hình đủ để kể cả toàn cảnh và từng bước

F1. Một traffic snapshot: paid cache → bid → candidate profiles → actor responses → next trajectory. Có một ca cải thiện và một ca thất bại/không cần sửa. Không chỉ chọn maximum oracle gain mà che learned decision.

F2. Controlled geometry/calibration: floor vs R và decision regret vs calibration N; empirical curve của strategy, scope T2 rõ. Không gọi E1b là exact Gaussian channel.

F3. Closed-loop quality vs total bytes trên learned actor, direct baseline hiện rõ, uncertainty qua actor/scenario seeds. Nếu chỉ fixed MP2 thì nhãn chính phải nói vậy.

F4. Mechanism: response-prediction errors on action-changing candidates, repair acceptance/harm, bid/no-bid/queue-bid, và offline-to-closed-loop transfer. Overall action accuracy dễ bị always-p1 đa số che tín hiệu; báo riêng những candidate thực sự đổi action.

Latency nếu thiếu space đưa bảng; không cần thêm 6 figure chỉ để giống paper 2026.

### P5 — viết bản gửi và đóng dự án, không đợi đóng mọi future work

Gợi ý bố cục tối đa 15 trang faculty template (điều chỉnh sau khi thầy xác nhận):
- Introduction + concrete example + related work: khoảng 2 trang.
- Problem/protocol/information/byte model: 1.5 trang.
- Methodology: algorithm + learning targets + safeguards: 2 trang.
- Theory: hai kết quả chính và scope, không cả bộ Lean: 2 trang.
- Experimental design: 1 trang.
- Results và failure analysis: 3 trang.
- Limitations/conclusion: 0.5–1 trang.
- References và phần còn lại trong tổng limit.

Đặt đúng tên section Methodology và Experimental Design. T1/T2 hỗ trợ thiết kế; Results không dùng theorem như thể đã chứng minh neural traffic guarantee.

Release cần có:
1. paper_marl.tex, bibliography, figures, compile được theo template.
2. Claim-to-evidence table; theorem files đã gate, statement/assumptions đúng.
3. One-command small reproduction + manifest/config/seed/checkpoint links; archive source versions dùng sinh figure.
4. Figure numbers sinh từ raw artifact, không gõ lại thủ công.
5. Anonymous PDF theo venue và kiểm references/limitations/censoring.
6. Artifact freeze một lần cuối; không rebuild tất cả Lean chỉ để đổi prose.

Không cần làm trước nộp: exact nesting upper, adaptive T2 optimality mọi tham số, pair tightness, all-budget confidence tables, generic actor drift, arbitrary-topology network, extra simulator, theorem cho mọi deep actor.

## 8. Điều kiện đóng và quyết định nếu kết quả còn âm

“Đủ để gửi một paper method MARL” không bằng “đã compile toán”. Cần:
- actor learned và protocol hợp lệ;
- contribution method được so trực tiếp với mạnh nhất trong scope;
- outcome closed-loop phù hợp headline, hoặc bản empirical study chủ động nêu kết quả âm;
- theorem không bị dùng ngoài giả thiết;
- bản thảo/figures/repro package hoàn chỉnh;
- track/deadline cho phép submission.

Nếu B4 âm, vẫn có thể làm actor pilot và target diagnostic để biết một adaptation cụ thể có đáng chạy. Không tự động bỏ CityFlow. Nhưng cũng không có lý do khoa học để bảo đảm sẽ thắng sau khi đổi actor.

Nếu các bước này vẫn âm hoặc deadline không cho phép, hai quyết định là khác nhau:
- **Đổi loại claim của bản gửi hiện tại** sang analytical/empirical limits có CityFlow evidence.
- **Bỏ dự án MARL** hoàn toàn.
Dữ liệu hiện tại chỉ buộc hạ một số claim, không buộc quyết định thứ hai. Chọn scope bản gửi phải do người dùng/thầy, không do worker âm thầm đổi tên mục tiêu.

## 9. Handoff ngắn cho worker

Ưu tiên ngay: hoàn tất B4 → chốt byte/protocol/target semantics → actor pilot → matched closed-loop comparison → manuscript/release.

Trong lúc chờ: viết manuscript và claim map ngay; sửa exact nesting claim; giữ request baseline v4; không còn “η certificate”; không đòi học Where2comm perception nguyên bản; không mở theorem tùy chọn.

Đọc bản này cùng MARL_E1_INDEPENDENT_AUDIT_20260927.md và MARL_CRITICAL_PATH_INDEPENDENT_RECHECK_20260927.md. Bản status mới đã sửa nhiều lỗi, nhưng chưa giải quyết các mắt nối protocol/byte/continuation/learned actor trên đây.


## 10. Cập nhật theo báo cáo worker vừa gửi và thứ tự bàn giao cuối

Đã đọc lại bản status cập nhật và BASELINES_DIRECT_STAGEA2_RESULTS; bốn correction đã được worker tiếp nhận. Không yêu cầu làm lại chúng. Kiểm lúc 23:52 EDT: controls B4 đã có 8/9 job, còn bid_queue seed 2; chưa có cl_dev/cl_test lúc kiểm. Đây là trạng thái trên đĩa, không phải ước lượng “còn 4 job” trong báo cáo trước.

Các quyết định nên giao thẳng, để tránh thêm vòng xin phép cho việc không chặn khoa học:

1. **Aesop/OLD7:** tách khỏi đường găng. Import tactic Aesop không tự là axiom bổ sung; kiểm dependency/axiom policy khác với cấm token tên tactic. Các gate MARL hiện hành đã PASS. Ghi OLD7 là historical tool-policy issue; sửa classifier lúc rảnh, không đổi gate đang chạy.
2. **Paper B supplement:** giữ nội dung correction toán tại dòng 398–402: eta=ch làm cả h^6 và eta^2 h^4 có order h^6. Không revert một correction đúng chỉ vì session khác sửa. Phần này không chặn MARL; nếu review cả diff lúc 14:02 thì chỉ giữ các thay đổi đã đối chiếu.
3. **Manuscript:** bắt đầu working draft ngay, ghi rõ kết quả chờ và limitation. Không có lý do đợi E3 mới viết problem/method/related work. Scope “formal theorem đã gate” vẫn được giữ.
4. **Git:** không git add toàn bộ cây. Lần kiểm này git status --porcelain --untracked-files=all thấy 18,655 untracked files và 17 tracked changes; đơn vị đếm có thể khác báo cáo 2,951. Chia danh sách: source/theory/docs/config nhỏ cần snapshot; model/data/results lớn cần manifest + nơi lưu; temp/build/runtime không đưa vào commit. Untracked nghĩa là chưa được Git bảo vệ, không chứng minh không tồn tại backup khác. Không xóa dữ liệu lịch sử hay tự commit công việc session khác.

### Checklist tuần tự, mỗi bước có output để review

| Thứ tự | Worker làm | Artifact/điều kiện xong |
|---|---|---|
| 0 | Xác nhận với thầy track, deadline, khả năng nộp muộn | Một dòng target chính xác; faculty/student không lẫn |
| 1 | Snapshot source/docs đang hoàn chỉnh, giữ nguyên producer chạy | Danh sách hash/commit chọn lọc; không gộp 18k file mù |
| 2 | Viết claim map + skeleton manuscript | .tex có Problem, Methodology, Theory, Experimental Design, Results, Limitations |
| 3 | Thu B4 theo endpoint khóa sẵn | Verdict + raw rows + every-seed report |
| 4 | Chốt protocol decode-budget/byte model, target continuation, R1/direct | Một định nghĩa toán và một runtime implementation cùng object |
| 5 | Nếu cần, diagnostic target mismatch trên development cố định | Hai bảng label cùng state, actor, randomness và horizon; không test fishing |
| 6 | Actor communication-aware một seed smoke | Checkpoint + runtime access checks + message-use diagnostics |
| 7 | Port local bid/response/evaluator sang actor mới | Train/runtime parity, không còn MP2 oracle coefficients |
| 8 | Freeze actor; tune method/direct/learned scheduler trên cùng tài nguyên | Config/model hashes và validation choices |
| 9 | Main runs nhiều actor seeds, fixed primary endpoint | Closed-loop outcome, bytes, paired uncertainty; không chỉ gain H=3 |
| 10 | Ablation bid vs no-bid/queue bid; R1 vs direct | Biết thành phần nào tạo lợi, kể cả kết quả âm |
| 11 | Một shift và compute benchmark rảnh máy | Phạm vi robust/latency được nói đúng; delay thật chỉ nếu giữ claim đó |
| 12 | Chốt 3–4 hình và bảng kết quả | Mọi số tái tạo từ manifest/raw data |
| 13 | Viết kết luận theo kết quả, anonymous PDF, release nhỏ | Bản gửi đúng track + script reproduce + limitations |

Không có bước “đợi full gate A/B/C” chen trước bước 2–10. Full gate toàn MODS là việc release/proof-corpus riêng; làm sau B4 khi máy rảnh nếu cần, không phải điều kiện để bắt đầu bản MARL.

### Figure 3 đã được nhìn trực tiếp

Bản v3 hiện có đúng nhãn fixed MP2 và corrected request baseline. Để đưa vào manuscript:
- Rút tên dài trong legend thành Prefix / Direct / Response-bid / Fresh-queue / Request / Oracle; giải thích ở caption.
- Chuyển run directory, hardware note và danh sách latency chưa đo sang caption/bảng. Hiện notes dài tràn khỏi vùng panel; font nhỏ không phù hợp bản in.
- Để legend ngoài vùng dữ liệu; giữ error bars và oracle ký hiệu rỗng.
- Ghi rõ lower waiting is better và đây là một operating point.
- Panel latency chỉ có hai điểm; cân nhắc thay bằng bảng để dành diện tích cho bid/no-bid và offline-to-closed-loop gap.

Lệnh tính lại bảng audit đã có, không train hay rollout:
    cd /Users/phanan/cig-amf-main
    python3 research/papers/audits/MARL_PUBLICATION_AUDIT_RECALC_20260927.py

Không đưa lệnh chạy E3 giả khi runner/input adapter chưa viết. Worker hoàn thành bước 6–7 phải cung cấp command thật từ CLI --help, config đã freeze và một smoke log trước khi giao người dùng chạy batch dài.
