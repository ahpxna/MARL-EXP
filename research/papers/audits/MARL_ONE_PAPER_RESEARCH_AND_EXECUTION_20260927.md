# Một paper MARL từ assets hiện có: hướng chốt, audit và đường hoàn thành

Ngày: 27/09/2026. Đây là đề xuất nghiên cứu và kế hoạch thực hiện, không phải báo cáo đã hoàn thành MARL. Không thay thế hay sửa các ledger của A/B/C. Các định lý mới đề xuất dưới đây chưa được tính là Lean đã chứng minh.

## 1. Quyết định nghiên cứu

**Hướng chốt: When Is a Communication Priority Enough? Learning and Repairing Budgeted Coordination in MARL.**

Câu hỏi: một đội agent điều khiển giao thông, chỉ nhận được một số message trước mỗi quyết định, có thể dùng một thứ tự ưu tiên rẻ cho mọi mức bandwidth khi nào? Khi không thể, vấn đề nằm ở score sai, ở cấu trúc optima không lồng nhau, hay ở thiếu dữ liệu để biết phải sửa gì? Cần bao nhiêu phép đo tương tác và bao nhiêu thay thế message để khắc phục, và lợi ích có còn sau khi tính chi phí thực thi?

Chuỗi của paper:

    học giá trị phối hợp của TẬP message
      → kiểm khi nào một priority đủ tốt
      → phân biệt lỗi score với giới hạn của mọi priority
      → mua thêm evidence chỉ để phân giải những lựa chọn sửa còn xung đột
      → sửa ít phần tử trước transmission
      → các actor đã học thực hiện joint control trong moving traffic.

Đây là một câu hỏi chung. Không tách thành ba hệ A/B/C cùng chạy trong một video. A là phần học/đo đủ tương tác; B là điều kiện đã biết đủ để chọn một repair; C là giới hạn của commitment và quyền sửa. Functional/D6 định nghĩa loss và tương tác, các paper cũ khác cung cấp công cụ tương ứng.

**Main application:** mạng agent điều khiển đèn giao thông trong CityFlow, dùng hạ tầng đang có. Đây là MARL nếu các actor điều khiển được train và cùng tối ưu team objective; heuristic max-pressure hiện tại chỉ là diagnostic. Không cần CARLA/Minecraft để hoàn thành bài. Có thể làm video từ moving traffic của chính benchmark.

**Điều không hứa:** không có literature search nào chứng nhận tuyệt đối không collision với mọi paper, và không có checklist nào bảo đảm accepted. Kết quả cần bảo vệ là một định luật và một algorithm cụ thể, không phải danh sách keyword chưa thấy ai ghép.

## 2. Đã đọc gì và bằng chứng nào được dùng

Lượt này đọc lại toàn bộ attachment `15bae459-5146-4093-a47d-e19f94b5153c/Pasted text.txt`, hai memo MARL trước, story verdict mới, protocol, ba module mới SubsetFrontier/NestingDegreeGeneral/ProxyBlindness, producer của hai diagnostic CityFlow, và JSON kết quả. Đọc nội dung liên quan của set_critic_probe và handoff generic recourse; không tuyên bố đã đọc lại mọi source của mười paper hay mọi dependency Lean trong lượt này.

Kết hợp với audit trước về bảy bản thảo cũ và A/B/C. Không dùng con số “1.000 full papers đã đọc”. Literature mới kiểm thêm floating feature selection, communication/coordination trade-off và active learning of communication structures; phân biệt full-text mở được với abstract/metadata.

**Nguồn trạng thái:**
- `work/p13_conjectures/LeanMarlSubsetFrontierV1.lean`
- `work/p13_conjectures/LeanMarlNestingDegreeGeneralV1.lean`
- `work/p13_conjectures/LeanMarlProxyBlindnessV1.lean`
- `research/marl_budget/P2_generic_layer/HANDOFF.md`
- `research/marl_budget/PROTOCOL_v0.md`
- `scripts/DIAG_cityflow_set_objective.py`
- `scripts/DIAG_cityflow_set_objective_hops.py`
- `research/marl_budget/diag_20260927/set_objective_full.json`
- `research/marl_budget/diag_20260927/set_objective_hops_full.json`

Source hash producer và env của cả hai JSON khớp file hiện tại khi kiểm. Không chạy lại experiment hay full gate để tạo số mới.

## 3. Tiến triển thật, và giới hạn phải giữ

### 3.1 Mathematical core hiện có

Với set value f, g_i=f({i})−f(∅), giả thiết

\[
 |f(A\cup\{i\})-f(A)-g_i|\le\delta,\qquad i\notin A,
\]

`subset_frontier` chứng minh: từ prefix P_k xếp theo g, với mọi tập T có k phần tử và mọi R, **tồn tại** S có k phần tử, cách P_k không quá R thay thế, thỏa

\[
 f(T)-f(S)\le 2\delta\bigl(|P_k\setminus T|-R\bigr)_+.
\]

`subset_zero_price`: cut margin ≥2δ đủ để prefix optimal. `subset_constant_sharp`: hệ số 2 đạt đúng trên một bảng ba message có gains bằng nhau. Không phải đã có family đạt cả frontier ở mọi R cho objective này.

`LeanMarlNestingDegreeGeneralV1`: hai tập mục tiêu xung đột ở budgets liên tiếp buộc bất kỳ chain nào có khoảng cách lớn ở ít nhất một budget; dựng lower bound tăng tuyến tính theo m. Matching upper tổng quát còn mở. Đây là set-system/distance-loss theorem, chưa là một communication game được dựng từ observation và executable actor.

`LeanMarlProxyBlindnessV1`: hai value tables trùng trên mọi empty/singleton; oracle một thay thế đạt optimum nhưng mọi rule chỉ đọc first-order information có worst-case regret ≥4, kể cả randomization. Một pair measurement chính xác phân biệt được chúng. Đây là cầu A đáng dùng, **chưa** là noisy sample-complexity theorem hay all-surrogate-optima starvation theorem.

Các file ghi compile sạch trong tiến trình, nhưng lượt này không làm lại import-closure gate. Không biến việc đọc source thành xác nhận gate.

### 3.2 Dữ liệu traffic mới nhất

| Diagnostic | Số bảng | Score order có gap R=0 | Best deterministic nested order có gap R=0 | Score order còn gap R=1 |
|---|---:|---:|---:|---:|
| One-hop max-pressure | 1.180 | 56/1.180 = 4,75% | 2/1.180 = 0,17% | 0 |
| Two-hop max-pressure | 708 | 124/708 = 17,51% | 5/708 = 0,71% | 23/708 = 3,25% |

Two-hop có m=5,6,7,8,10. R=2 còn score gap tại 1/708 bảng. Best deterministic nested order có zero gap sau R=1 ở toàn bộ các bảng đã chạy. Đây không phải theorem mọi traffic instance.

Các bảng không phải những training seeds độc lập. Mỗi bảng là một (state, ego intersection) dưới controller cố định; các agent khác được giữ ở action từ full communication. f_i(S) chỉ thay thông tin/action của ego rồi rollout H=3 decision steps. Vì vậy:

- đây là ORACLE DIAGNOSTIC của unilateral intervention;
- chưa có learned MARL thắng baseline;
- chưa đo tất cả agent cùng bị hạn chế thông tin;
- chưa phải expected infinite-horizon team return;
- G trong script là min_order max_budget, không phải randomized min_distribution max_budget expectation.

**Hệ quả định hướng:** dữ liệu hiện tại ủng hộ “score đơn lẻ đôi khi bỏ lỡ tương tác” nhiều hơn “mọi nested order đều tệ”. Không được dùng 17,51% làm evidence cho intrinsic price of nesting. Nhánh không cần repair là một dự đoán tích cực cần đo, không phải che kết quả âm.

## 4. Các lỗ hổng kế hoạch cũ chưa xử lý đủ

1. **Existence ≠ algorithm.** Proof đi từ prefix về một T optimal đã biết. Greedy best-one-swap hoặc repair head chưa được proof này bảo đảm tìm ra witness. Local optimum có thể mắc kẹt vì complementarity. Phải có search error/candidate coverage term hoặc exact solver nhỏ.
2. **Hai objective khác nhau.** D6 half-oscillation compression loss có coefficient δ; actual subset decision value ở module mới có 2δ. Không đổi tên cùng một objective, không bê coefficient giữa hai bên.
3. **Ba notion of interaction.** δ_local ở SubsetFrontier, δ_D6=max over i,x,c, và δ_pair không đồng nhất. D6 bound suy δ_local≤δ_D6. Pairwise sampled maximum không phải upper certificate cho i-versus-rest interaction. Phải ghi field riêng trong artifact.
4. **Từ bảng f đến actor còn thiếu.** sharpF có giá trị nonmonotone, có thể phù hợp fixed imperfect decoder; nó không tự là Bayes-optimal value of free information, vì decoder optimal có thể bỏ qua thêm thông tin. Phải dựng game/decoder hoặc nói rõ fixed-controller interpretation.
5. **Đính chính: không có lỗi chọn optimum trong `distance_regret_lower`.** Với loss ℓ_k(S)=|S\O_k| và |S|=|O_k|=k, loss bằng zero khi và chỉ khi S=O_k. Optimum là duy nhất; obstruction của theorem do đó đã bao quát mọi optimum. Tôi rút phê bình trước đối với theorem này. Cảnh báo về nhiều optima chỉ áp dụng khi chuyển sang một objective learned-traffic KHÁC: không được chọn tùy ý một optimum ở mỗi budget rồi suy toàn bộ tập optima không có chain. Nó không phải gap cần sửa trong distance-loss construction hiện tại.
6. **m≥7 bị diễn đạt sai.** m≥7 liên quan khả năng cần hơn một revision của best chain trong các phép kiểm hệ tập. Một revision vẫn có thể giúp đáng kể ở m=3. `PROTOCOL_v0.md:140` đang nói quá rộng “must grow ... before revision can matter”.
7. **Không từ local diagnostic suy global savings.** Khi nhiều receiver cùng đổi messages/actions, f_i được đo với tất cả agent khác full-information không còn là objective tương ứng.
8. **Self-check không phải lúc nào là test.** Producer one-hop ghi check “deployed runs used no oracle data” với `ok: True` cố định. Đây là assertion trong báo cáo, không phải phép kiểm có thể fail. Cần access-log assertion thực sự; hiện không suy ra deployed code đã rò từ riêng finding này.
9. **Raw audit chưa tái dựng hết được.** Hai JSON giữ summaries/per-budget values nhưng không giữ full subset→action→rollout-value table. Muốn kiểm độc lập δ và optima phải lưu bảng thô hoặc checkpoint và replay seed có thể tái dựng.
10. **A chưa đầy đủ.** Two-world blindness hiện gains đều zero, chưa có một positive surrogate optimum Γ_f cùng sacrifice law. Không được gọi nó là đã instantiate toàn bộ Paper A.
11. **Revision count không là latency.** Một best-one-swap tốn k(m−k) candidate evaluations. Một budget-conditioned network có thể rẻ hơn. Comparator này bắt buộc.
12. **Certificate có thể vacuous.** Mọi finite f có một δ nào đó không đủ; phải đo certificate tightness và coverage trên held-out states. Sampled δ thường là lower estimate, không phải safe upper bound.

Không sửa các file worker đang làm trong lượt này. Những sửa tài liệu/provenance này thuộc WP0 dưới đây.

## 5. Novelty phải đặt ở đâu, sau literature audit

| Neighbour | Phần đã có | Target khác cần chứng minh ở đây |
|---|---|---|
| Universal/incremental optimization | Một ordering phục vụ nhiều cardinalities; approximation | Interaction-sensitive bounds và executable learning/repair cho team decision, không claim universal order mới |
| Recoverable robust selection | Commit rồi đổi một số phần tử sau uncertainty | Late communication budget, learned information access, cost để BIẾT sửa gì |
| Floating feature selection | Thêm/bớt features để thoát nesting | Không claim swapping mới; phải thắng matched local-search baseline và có quantitative acquisition/repair law |
| SchedNet (ICLR 2019) | Shared bandwidth, học ai broadcast, message encoding và action selection | Global-budget broadcast architecture không được tính là novelty; phải so nesting/revision/acquisition law và lợi ích thực thi với baseline SchedNet được điều chỉnh cùng information/timing contract |
| CASEC, SOP-CG, NDQ, MUTE | Task-relevant topology/messages, giữ decision/return, tractable coordination | Phân biệt score price/nesting price/information deficit; criterion cho lúc nào không cần sửa và chi phí sửa có evidence |
| DRD, multiple-answer pure exploration | Dừng khi biết một acceptable answer | Acceptable repairs có constraint R và budgets; dùng theory này làm công cụ, không phát minh decision-before-identification |
| Active learning of MAS communication structure | Chọn training tasks để học graph dưới cost | Chọn evidence để phân giải một repair còn không xác định, kèm lower/upper trong controlled family |
| Ask-type MPOMDP communication | So value of communication với coordination cost | Không claim first to ask only useful information; chốt structural + acquisition law cụ thể |

Nguồn trực tiếp để review:
- [SchedNet, ICLR 2019](https://arxiv.org/abs/1902.01554): primary abstract xác nhận shared bandwidth, learned broadcast scheduling, encoding và action selection. Đối chiếu này đủ bác claim novelty của kiến trúc đề xuất; không từ abstract suy rằng paper không có một kết quả phụ nào về budget.
- [Incremental submodular maximization, 2026](https://arxiv.org/html/2606.28558v1), model/Theorems 1–2: monotone submodular; bound kiểu competitive ratio. Không tự áp dụng cho arbitrary interacting message value.
- [Recoverable robust selection, Chassein et al.](https://eprints.lancs.ac.uk/id/eprint/87346/1/paper.pdf), model: fixed cardinality, uncertain costs, bounded exchanges. So sánh đúng model, không chỉ title.
- [Floating search, Pudil–Novovičová–Kittler 1994](https://doi.org/10.1016/0167-8655(94)90127-9). Publisher abstract xác nhận dynamic additions/removals; bản full institutional PDF tìm thấy nhưng fetch timeout. Không claim đã audit hết theorem của nó.
- [CASEC](https://arxiv.org/pdf/2106.02886), [SOP-CG](https://proceedings.mlr.press/v162/yang22a.html), [MUTE](https://arxiv.org/html/2607.03473v1): giữ là closest MARL comparisons theo memo trước.
- [Active Learning for Communication Structure Optimization in LLM-Based MAS](https://arxiv.org/html/2605.05703v2), §4 Eq.2–4: graph-performance optimization rồi information gain over graph parameters; §4.4 active task selection. Đã đọc phần method, không đọc lại mọi appendix. Do đó “active learning communication structures” riêng nó không mới.
- [Asking for Information ... Multi-Agent POMDPs](https://doi.org/10.1109/LRA.2026.3703246), [author repository](https://iris.polito.it/handle/11583/3013129): publisher search content và repository abstract xác nhận ask-type communication/coordination tradeoff. Direct full-text mở bị challenge; giữ mức kiểm tra đó.

Không tìm thấy equivalent đầy đủ trong nhóm đã kiểm **không** chứng minh priority. Cận near-modular bằng telescoping khá cơ bản; riêng bound 2δ cộng game ba message có thể chưa đủ một paper MARL mạnh. Phần phân biệt đáng đầu tư là biến geometry đó thành một phương pháp học/kiểm/sửa thực thi được, có sample-cost result và kiểm định trên learned traffic.

## 6. Tận dụng đủ assets: mỗi asset có một nghĩa vụ kiểm được

| Asset | Dùng ở đâu | Deliverable để được tính là dùng thật |
|---|---|---|
| A | Acquisition học set interactions, tránh first-order starvation | Noisy repair-identification theorem + proxy vs repaired acquisition experiment; muốn claim full A phải thêm positive Γ_f bridge |
| B | Dừng đo khi tồn tại common acceptable repair | Measurable stopping rule, failure coverage; comparison với reconstruct toàn bảng/identify world |
| C | Pre-budget priority, budget-aware reference, R substitutions | Same-law/feasible-protocol definitions; giữ randomization/timing đúng; generic frontier |
| Master | Calibration của nuisance/noisy probes | Explicit observation kernel, estimated nuisance sensitivity hoặc cite phần áp dụng; không copy một theorem calibration không instantiate |
| Functional | Quyết định thật, không lấy attention làm loss; drift/certificate lifetime | f từ actions/rollouts; critic/action/return bridge; refresh rule với drift term |
| Support | Common answer, joint feasibility; pairwise không đủ | Một joint repair/coordination answer hợp lệ cho mọi plausible world, không ghép local safe actions tùy tiện |
| Query | Quyền truy vấn quyết định thông tin có thể có | Singleton-only / pair / richer-menu ablation, cùng cost accounting; chỉ đọc exponent nếu đã dựng đúng channel |
| Structural | Một rank, menu ranks, optimum từng budget; timing | Best-rank vs score-rank diagnostic; menu baseline; comparator có cùng information |
| Adaptive | Adaptive observation allocation, confidence, refresh | Log sample counts và valid stopping; frozen-actor rounds tránh nonstationarity ngầm |
| D6 | Margin/interaction sufficient regime | Actual local-interaction bridge; score certificate và empirical coverage, không dùng pairwise score làm bound |
| Code/models/gates/results | Tránh xây lại pipeline | Reuse budgeted env/cache/rank components; clone-in-test oracle labels; hash + traceable gate |

“Tận dụng tất cả” nghĩa là mọi asset được dùng đúng vai trò hoặc được ghi rõ là không cần để chứng minh một claim. Không có lý do copy mọi hằng số, every parity family, mọi exponent vào main paper. Chúng vẫn là antecedents/appendix/validation cases; không giả vờ cùng áp dụng cho neural traffic.

## 7. Mathematical target chính xác

### 7.1 Chốt một objective và một information contract

Cho public/cached context z, unknown interaction world θ, message item set E. Một decoder/actor profile đã đóng băng D biến own observations và received messages thành executable joint action. Định nghĩa f_{θ,z}(S) bằng expected team decision value với đúng decoder ấy, cùng continuation/evaluation rule cho mọi S. Không cho selector biết θ hay current unreceived payloads.

Prefix P_k(π), distance d(S,T)=|S\T| cho equal-size sets. Reachable sets F_R(π,k)={S:|S|=k,d(S,P_k(π))≤R}. Oracle price

\[
 G_{\theta,z,R}(\pi,k)=\max_{|T|=k}f_{\theta,z}(T)-\max_{S\in F_R(\pi,k)}f_{\theta,z}(S).
\]

Đây là geometry; oracle không được đóng giả runtime method. Best deterministic rank, random max-E và E-max là ba object khác nhau.

N là **paid calibration/interaction rollout count**, R là **pre-transmission replacements**, k là **runtime packets**. Giai đoạn đầu không đồng nhất một simulator rollout với một wireless message. Runtime sensing extension phải tính thêm time/bytes riêng.

### 7.2 Cầu learned-score → repair, đã dẫn trên giấy, cần formalize

Giả sử |g_i−ĝ_i|≤u, δ là true upper bound cho local interaction, và P là top-k theo ĝ. Cùng exchange path trong SubsetFrontier cho

\[
 \exists S\in F_R(P,k):\quad f(T^*)-f(S)
 \le2(\delta+u)(d_k-R)_+,
\]

với d_k=min_{T* optimal}|P\T*|. Lý do: mỗi surviving mismatch có true score deficit nhiều nhất 2u; residual exchange tốn nhiều nhất 2δ.

Nếu fhat có uniform error ε trên F_R và solver tìm Ŝ có fhat(Ŝ)≥max_{F_R}fhat−ν, thì

\[
 f(T^*)-f(\widehat S)
 \le2(\delta+u)(d_k-R)_+ +2\varepsilon+\nu.
\]

Nếu chỉ search candidate family C⊂F_R, cộng

\[
 \zeta=\max_{F_R}f-\max_C f.
\]

Không được bỏ ζ khi một learned proposal head chỉ sinh vài swaps. Nếu estimates stale, cần current-error bounds hoặc đưa drift vào u, ε; tránh tính drift hai lần.

Sufficient zero-price certificate: estimated cut margin ≥2δ+2u. Với δ chưa biết, thay bằng **upper confidence bound** δ_U, không sampled max. Đây là ứng dụng elementary exchange/error inequalities, không claim novelty riêng của bất đẳng thức 2ε.

### 7.3 Warm-up giới hạn: noisy observations của một arbitrary set-value oracle

**Scope được sửa:** `sharpF` là nonmonotone. Các phép tính bên dưới hợp lệ cho việc đo một bảng payoff bất kỳ, hoặc một fixed imperfect decoder SAU KHI dựng được realization; chúng chưa chứng minh một communication model với Bayes-optimal decoder. Nếu bộ giải mã tối ưu được phép bỏ qua message thêm vào, giá trị thông tin phải không giảm theo inclusion, nên `sharpF` không có interpretation đó. Vì vậy §7.3 chỉ là unit example cho quyền sửa và thông tin để sửa, không đóng bridge ở §4.4 và không phải headline theorem MARL. Không có lỗi toán do nonmonotonicity trong lớp arbitrary set functions; lỗi của bản kế hoạch trước là chưa ghi rõ giới hạn này ngay tại warm-up.

Đặt f_+=h·sharpF và f_-=h·mirrorF, h>0. Queries được phép đo f_w(S) + Gaussian noise variance σ². Empty/singletons có cùng mean 0; {0,2} có cùng mean 3h; hai informative pairs có means ±7h. Fix k=2, initial P={0,2}.

- R=0: regret=4h dù có vô hạn dữ liệu.
- R=1, oracle biết world: regret=0.
- Chỉ first-order observations: randomized worst-case expected regret≥4h.
- Với tolerance 0<ε<4h, mỗi world có đúng một ε-acceptable pair. Đòi failure probability≤α<1/2 ở cả hai world.

Mỗi informative-pair measurement có KL

\[
 \kappa=\frac{(14h)^2}{2\sigma^2}=\frac{98h^2}{\sigma^2}.
\]

Stopped change of measure, khi protocol hypotheses thỏa, cho

\[
 E_+N_{\rm inf}(\tau)\ge\frac{\sigma^2}{98h^2}\,
 \operatorname{kl}(1-\alpha,\alpha).
\]

Upper: đo {0,1} n lần độc lập rồi xét dấu sample mean; đủ

\[
 n\ge\left\lceil\frac{2\sigma^2}{49h^2}\log\frac1\alpha\right\rceil.
\]

Nếu learner dành ≤β Eτ informative samples thì Eτ≥σ² kl/(98βh²). Nếu pathwise N_inf(t)≤c0+c1√t thì Jensen cho

\[
 E\tau\ge\left[\frac{(\sigma^2\operatorname{kl}(1-\alpha,\alpha)/(98h^2)-c_0)_+}{c_1}\right]^2.
\]

Đây là một extension suy ra trên giấy từ source hiện tại và Gaussian testing; chưa là theorem mới đã gate. Nó nối **có quyền sửa** với **có thông tin để sửa**. Không gọi elementary two-point testing là invention. Để tích hợp full A, còn phải chứng minh acquisition tối ưu theo một surrogate Γ_f>0 thực sự buộc β nhỏ, trên cùng world model; hypothesis “β nhỏ” không được đổi tên thành kết luận A.

### 7.4 Phần B cần thêm để không chỉ là testing hai world

Dựng ít nhất một finite team-message family với nhiều world, acceptable repairs overlapping và không có globally common repair ở đầu. Acceptable set phải tính từ actual joint loss và F_R, không gán nhãn safe tùy ý. Chứng minh query/stop khi common acceptable repair xuất hiện, trong khi exact identification còn chưa xong. Chỉ thêm h-order separation nếu channel thật thỏa KL/Hellinger assumptions; không cần tái tạo toàn bộ parity endpoint để có một đóng góp MARL.

Đích mạnh: trên cùng family, recourse thay đổi feasible acceptable repairs và vì vậy thay đổi lượng evidence cần. Counterexample/lower bound và constructive upper phải dùng cùng query access, decoder, tolerance, budgets.

### 7.5 Cầu tới return

Không suy rollout value H=3 dưới held action thành Q của deployed policy. Chọn finite-horizon theorem hoặc discounted one, ghi continuation policy. Dùng performance-difference lemma với occupancy của policy bị nén, actor/search error và critic error. Cần joint-action feasibility; không suy mỗi actor tốt cục bộ thành jointly optimal. Neural TD error không tự cung cấp uniform critic error.

Controlled model: chứng minh đầy đủ. Moving traffic: đo empirical extension với reward/latency/shift, không tuyên bố theorem covers arbitrary MARL learning convergence.

## 8. Protocol thực dụng nên chọn

**Ứng viên triển khai, không phải contribution mới:** một learned actor profile, một network-wide packet budget, và public scheduler. Kiến trúc broadcast dưới bandwidth chung đã có ở SchedNet; baseline đó là bắt buộc nếu chọn ứng viên này. Mỗi intersection là một agent có local sensor; selected packets được broadcast qua infrastructure. Scheduler dùng cached history/topology/age và metadata đã tính phí; không đọc all fresh payloads. Actors nhận own observation + delivered packets và tự chọn phase. CTDE cho phép global state trong training, không trong execution selector.

Global packet budget thuận tiện vì feasible family đúng dạng |S|=k của core theorem và đo ảnh hưởng tới joint action. Đây chỉ là tiện lợi mô hình hóa, không đủ lý do đổi bài toán thực tế hay bỏ protocol đang có. Cần kiểm grant đến muộn và precommitment có ý nghĩa hệ thống, và so trực tiếp với selector nhận budget rồi chọn tập từ đầu. Nếu không có lợi ích compute/latency hoặc nhu cầu commitment thật, không ép runtime vào priority để tạo lợi thế giả. Hạ tầng CityFlow v0 là per-receiver budget: giữ nó làm diagnostic/ablation, thêm adapter broadcast riêng. Nếu quyết định giữ per-receiver caps cho main, phải phát biểu partitioned feasible family và proof riêng, không dùng uniform-cardinality theorem nguyên xi.

Một round:

1. Public context z_t từ thông tin thực sự đã nhận trước đó. Own observation mới chỉ ở agent chủ sở hữu.
2. Rank head tạo π_t trước grant. Precomputation/cache vẫn tính compute, không biến thành free offline work.
3. Bandwidth grant k_t tới; budget-conditioned selector của baseline được thấy cùng k_t ngay lúc này.
4. Kiểm certificate; nếu chưa đủ, repair head sinh legal candidates, evaluator chấm từ permitted inputs. Không biết optimum thật.
5. Chọn final S_t, tính d(S_t,P_k(π_t))≤R. Gửi request + packets + control metadata; count bytes theo multicast/unicast thực tế.
6. Delay tiêu thụ simulation time; actor control; traffic tiếp tục, cache ages cập nhật.
7. Log actual resources, hành động, reward, violations/timeouts. Oracle branch không tham gia chọn deployed action.

N trong theorem đầu tiên là interaction calibration rollouts giữa các frozen-policy rounds. Moving execution không được dừng simulation để đo oracle table. Runtime paid sensing nếu thêm sau là một experiment riêng với delay, không lẫn với training rollouts.

## 9. Algorithm cần xây, không chỉ “rank rồi swap”

Tên làm việc: **Learn–Check–Revise**, tên mô tả, không phải claim prior chưa có.

### Training/calibration

- Train communication-aware actors bằng CTDE, random masking trên budget range; chung encoder và training distribution giữa các selectors.
- Freeze actors trong một calibration round. Dataset chứa public context, legal mask, counterfactual joint action, rollout outcome, noise seed, cost.
- Fit set evaluator fhat(z,S); fit rank head bằng objective nhiều budgets. Không dùng attention weights thay singleton gains nếu claim theorem cần đúng gains.
- Học proposal head đưa ra R replacements hoặc một candidate menu. Keep incumbent prefix trong candidates.
- Acquisition learner chọn thêm (context, subset/probe) mà uncertainty còn ảnh hưởng tới quyết định selector. So với singleton proxy, uniform masks, information-gain và full-table reconstruction.
- Dừng calibration ở finite controlled model khi một candidate repair có valid certificate. Trong neural generalization setting, report empirical calibration/error trên held-out data, không gọi ensemble variance là formal confidence.
- Khi actor thay đổi, version actor/evaluator/data; old confidence không tự còn đúng. Functional lifetime/drift hoặc reset calibration phải áp dụng.

### Runtime

- Cheap ranking; k reveal; certificate check nếu được hỗ trợ.
- Nếu certificate đủ: giữ prefix.
- Nếu chưa đủ: evaluate incumbent + candidate swaps; chọn best feasible candidate theo same evaluator.
- Bound R là replacements so với original prefix, không phải số thao tác search lặp. Search có thể nhiều evaluations dù final distance nhỏ; log cả hai.
- Nếu deadline không đủ: giữ incumbent, report missed certification/deadline; không báo đã đạt oracle frontier.

### Certificate hữu hạn khả thi

Với simultaneous valid intervals L_n(S)≤f(S)≤U_n(S) trên feasible repair set, chọn incumbent có L lớn. Dừng khi

\[
 \max_{T\in F_R}U_n(T)-L_n(S_n)\le\epsilon.
\]

Nó bảo đảm ε-optimal trong reachable set trên coverage event. Relative-to-global-optimum cần thêm structural price. Candidate-only maximum chỉ chứng nhận candidate optimum; muốn toàn F_R phải có upper bound cho phần chưa enumerate. Khi sampling adaptive, dùng confidence sequences hoặc finite-sample allocation đã chốt, không optional-stop một fixed-n interval.

Đây là standard best-answer machinery; novelty cần là cách reachable geometry/query limitations tạo ra một quantitative obstruction, và được chứng minh/đo trong cùng pipeline.

## 10. Work packages tuần tự, đủ cụ thể để worker làm

Các đường dẫn mới dưới đây là **planned files**, chưa tồn tại chỉ vì được ghi ở đây. Mỗi WP phải xuất bằng chứng, không đóng bằng một docstring. Không có yêu cầu tạo nhiều agent hoặc nhiều simulator.

### WP0 — Chốt object và dọn những sai lệch đang có

**Input:** các source/artifact ở §2; `PROTOCOL_v0.md`.

**Làm:**
1. Ghi protocol v1 như §8; chốt broadcast hay per-receiver. Quyết định mặc định ở đây là broadcast main/per-receiver diagnostic.
2. Đặt tên riêng f_joint, f_ego_oracle, D6_loss; delta_local, delta_D6, delta_pair; V_det, V_rand. Ghi retention/removal orientation, max-E/E-max.
3. Sửa nhận định m≥7, stale “not formalised” ở set_critic_probe, và status “No learning ... nothing ... result” để tách diagnostic đã có với learning chưa có.
4. Thay hardcoded oracle-access self-check bằng counter/access-log assertion có negative test. Lưu full f-table/actual action/rollout seed trong output mới, không overwrite artifact cũ.
5. Cập nhật bảng nguồn→claim→scope→gate trong một report riêng; không coi theorem cùng tên là cùng statement.

**Output:** `research/marl_budget/PROTOCOL_v1.md`, versioned diagnostic schema, test access boundaries.
**Đạt khi:** có thể chỉ ra ai biết từng input tại từng stage; mọi resource cost và comparator đều cùng contract; output cũ giữ nguyên và có caveat.

### WP1 — Đóng hai chiếc cầu toán thiết yếu

**Input:** SubsetFrontier, ProxyBlindness, B transcript/observation kernels, A stopping machinery.

**Làm:**
1. Viết `LeanMarlEstimatedRevisionV1.lean`: estimated-gain bound, current uniform error, ν-search/ζ-candidate terms, margin certificate. Chứng minh assumptions satisfiable.
2. Viết `LeanMarlNoisyRepairV1.lean`: scaled two-world model §7.3; instantiate Gaussian observation law; transcript KL for adaptive/stopped protocol; matching order upper; informative-sample budget lower.
3. Không nhận “one pair identifies” làm noisy theorem: exact query và Gaussian repeated queries là hai channel.
4. Nếu claim optimized proxy allocation, dựng Γ_f>0 và prove optimizer/near-optimizer missing informative pairs. Nếu chưa có, theorem headline chỉ là restricted-information failure + paid repair; ghi nghĩa vụ này vẫn mở.
5. Viết finite actor/observation realization cho ít nhất một witness. Không chỉ set reward=f(S) trực tiếp cho scheduler rồi gọi là emergent communication.

**Output:** hai module mới + game model hoặc proof appendix toán đọc độc lập; claim ledger riêng của MARL.
**Đạt khi:** same world/channel/decoder cả lower và upper; mọi error parameter khác tên; không thêm giả thiết tương đương kết luận; clean gate sau source freeze do worker chạy.

### WP2 — Làm phần B thành thuật toán có điểm dừng

**Làm:**
1. Chọn family ≥3 worlds có overlapping acceptable repairs từ joint loss.
2. Ghi acceptable set phụ thuộc (π,k,R,ε); kiểm không empty ở mỗi world trong regime claim feasible.
3. Dùng confidence set thật để suy common executable answer; error≤α từ coverage. Không ghép các local acceptable actions nếu joint tuple không feasible.
4. Implement reconstruction-first và repair-first bằng cùng queries, same confidence/error target.
5. Nếu dùng order invariant s*, verify finite query assumptions và constants uniform trong signal domain. Chưa chứng minh thì chỉ đo count, không fit exponent rồi gọi theorem.

**Output:** `models/marl_repair_acquisition.py` và finite-model evaluator; optional Lean wrapper sau khi definitions đúng.
**Đạt khi:** có trường hợp dừng đúng khi world chưa identify, có trường hợp buộc đo thêm, có kiểm false-certificate rate và censoring. Đây mới là B xuất hiện thật.

### WP3 — Joint-control objective và data collection

**Làm:**
1. Reuse `envs/external/cityflow_budgeted.py` để thêm adapter main theo protocol v1, giữ byte-level delivery/cache.
2. Chuyển one-ego probe sang joint subset probe: cùng một S thay delivered observations của toàn bộ actor profile theo broadcast contract. Fixed continuation và rollout horizon ghi rõ.
3. Train một actor profile cơ sở có learning curves, checkpoint selection theo validation traffic; không dùng max-pressure làm “trained MARL”.
4. Giữ hai loại evaluator: privileged oracle để audit/labels; deployable fhat chỉ dùng z,S. Test bằng cách thay hidden payloads mà giữ allowed inputs: selection trước truyền phải không đổi.
5. Oracle comparison ở cùng true snapshot là retrospective reference; main learned selector đánh giá trên held-out trajectories khác.

**Output:** `scripts/DIAG_marl_joint_set_value.py`, `models/marl_set_value.py`, actor training config, full raw tables.
**Đạt khi:** ít nhất hai learned agents cùng quyết định; budgets restrict actual information; không dùng sum của ego-oracle tables thay joint objective.

### WP4 — Mechanism pilot trước training lớn

**Làm:**
1. Small finite game: exact value tables và LP/DP oracle, R=0..diameter, deterministic/randomized objectives giữ riêng.
2. Trên learned traffic actor đã freeze: small packet pools đủ enumerate; include low-interaction và high-interaction snapshots lấy bằng sampling rule đã chốt, không chỉ chọn những state method thắng.
3. Đo score price, best-rank price, repair-search gap, δ/margin, classifier/certificate error. Tie-breaking/permutation labels randomised hoặc swept để không thắng do index.
4. Có direct budget-conditioned head, greedy additions, best-one-swap/floating local search với matched evaluator-call budget.
5. Đo compute wall-clock trên target device, precompute lẫn post-reveal, không dùng count R thay latency.

**Output:** `scripts/EXP_marl_mechanism.py`, `mechanism_v1.json`, raw tables, claim-specific plots.
**Đạt khi:** biết benefit nằm ở học scores, chọn evidence hay recourse; giả thuyết runtime có evidence hoặc bị loại công khai. Nếu mọi learned-state gap nhỏ, không bỏ các state đó để quảng cáo frontier.

### WP5 — Learned method và comparator thực thi

**Làm:**
1. Reuse KPrefixNet chỉ sau khi xác nhận pre-budget head không nhận k; nhiều K-head chọn sau reveal không phải universal order.
2. Build repair proposal + evaluator như §9; incumbent luôn legal; compare actual search gap với exhaustive oracle ở small m.
3. Direct budget-conditioned selector dùng cùng z,k, encoder size tương đương và training compute comparable.
4. Actor-matched track: freeze cùng actor, thay selector/acquisition. End-to-end track: train toàn bộ methods với cùng environment steps và tuning budget, report riêng.
5. A ablation 2×2: proxy/uniform-or-repaired acquisition × no-revision/revision. Tổng simulator interactions, selection cost và calibration data đều tính.
6. Calibration rounds freeze actor; log checkpoint/data lineage và refresh. Không force exploration counts “đúng theo lịch” nếu implementation không bảo đảm.

**Output:** `models/marl_priority_repair.py`, runner/config/schema, same-budget baseline suite.
**Đạt khi:** không oracle execution; implementation can select on permitted inputs; all components ablated; mỗi module đóng một failure mode có số liệu.

### WP6 — Moving traffic evaluation chính

**Design ban đầu, cần pilot power rồi freeze:** train trên 3×3/4×4 network; test held-out arrival seeds, demand profiles, network size/topology; có fixed, bursty và abrupt-drop budget traces độc lập demand, rồi stress test correlated congestion/bandwidth. Dùng same traces cho paired comparison.

**Metrics:** network queue/delay, throughput và fraction demand served; unfinished vehicles/timeouts riêng; bytes gồm request/header/payload/metadata; peak bandwidth; message age; selector latency p50/p95/p99; inference/evaluator calls; calibration rollouts; team return. Mean travel time chỉ trên xe hoàn thành không đủ.

**Statistics:** pilot 3 independent training seeds để chọn variance/budget, sau đó tối thiểu 5 hoặc 10 nếu intervals còn rộng; evaluation episodes paired nhưng training seed là independent unit chính. Chốt practical effect size trước final runs. Không coi 1.000 correlated state tables là 1.000 independent training replicates. Report per-budget, per-demand, low/high interaction; không chỉ pooled mean.

**Baselines tối thiểu:**
- no-communication/full-communication references với actual controller quality report;
- learned score/universal rank R=0;
- random/greedy universal order;
- matched floating/best-swap search;
- direct budget-conditioned selector trained across budgets;
- menu of a few rankings, matched storage/inference;
- one strong scheduling baseline (SchedNet/ETC-style reproduction) và one task-value/communication-pruning comparator (CASEC/MUTE-inspired chỉ khi protocol-compatible).

Implementation sửa từ prior phải ghi adapted, không đặt tên bản gốc rồi tuyên bố faithful reproduction. Không lấy LLM MAS method làm traffic baseline chỉ để đủ danh sách. Budget-specific retrained policies/oracle để reference, ghi rõ thêm training budget.

**Output:** `scripts/TRAIN_marl_budgeted.py`, `scripts/EVAL_marl_budgeted.py`, configs, checkpoints, frozen manifests, per-episode JSONL. Các tên là interfaces cần worker tạo, không phải lệnh có sẵn để chạy ngay.
**Đạt khi:** lợi ích không biến mất khi charge all resources và so với direct head; regime không lợi ích được báo; deadline/latency có ý nghĩa trên hardware thật, không đặt deadline nhân tạo để loại đối thủ.

### WP7 — Những figures thực sự kể câu chuyện

1. **Hai nguyên nhân khác nhau:** cùng một state, plot best-per-budget set, learned score prefixes và best possible rank; overlap chỉ ra sai score hay intrinsic nonnesting.
2. **Geometry→regret:** realised repair gap vs bound; separate δ_local và certificate upper; coverage/tightness, margins. Không vẽ lower sampled interaction như certified bound.
3. **Evidence→repair:** calibration queries vs actual repair regret/false-stop, proxy/uniform/task-aware; show còn nhiều plausible worlds nhưng common repair đã tồn tại.
4. **N×R:** heatmap actual loss ở các measurement budgets và replacement budgets, k fixed/small panel. Điều này làm A+B+C nằm trong cùng một empirical object.
5. **Moving traffic Pareto:** delay/throughput vs actual bytes; annotate inference time và compare direct selector. Một point không có latency evidence không được quảng cáo “cheap repair”.
6. **Budget shock:** time-aligned trace budget, selected messages, revisions, age, queue and throughput; show method phục hồi và negative regime. Đây cũng là storyboard video.

Figure 1–4 controlled/diagnostic; figure 5–6 learned closed-loop. Không dùng video đẹp thay số liệu.

### WP8 — Đủ để đưa cho giáo sư/reviewer: điều kiện kết thúc

Chỉ chuyển sang writing/final submission package khi:

- model, timing, admissible information, cost semantics đã freeze;
- core theorem có statement gắn actual objective; mới/cũ/consequence được phân rõ;
- ít nhất một noisy acquisition/repair result đã nối, không chỉ generic testing lemma rời rạc;
- executable selector có uncertainty/search-gap treatment, biết phần guarantee nào conditional;
- có trained moving MARL, strong direct-selector baseline, đủ independent training seeds;
- controlled signatures và practical return/resource effects đều đo; không cherry-pick negative results;
- proof→code→artifact→figure audit, source/config/checkpoint hashes và censored outcomes đầy đủ;
- closest-prior comparison ở model/theorem/algorithm level, gồm floating selection và adaptive communication mới;
- abstract không claim first universal ranking, first recourse, first active sensing hay first decision sufficiency.

Đây là điều kiện tạo một submission có cơ sở. Reviewer vẫn có thể đánh giá novelty/importance khác; không có bảo đảm publication.

## 11. Việc bắt buộc, việc không nên làm chặn đích

**Bắt buộc cho câu chuyện đã chốt:** WP0–WP6, các figures chính, noisy information-to-repair bridge, actual control mapping và estimator/search validity. B phải hiện bằng common-answer stopping hoặc một experiment tương ứng có guarantee ở controlled setting; A phải có acquisition cost thật.

**Không bắt buộc trước submission:** exact worst-case R*(m) upper cho mọi m; mọi M3/M5/old7 theorem formalized lại; full exponent hierarchy trên neural observations; convergence theorem cho deep MARL; cả CARLA lẫn MetaDrive lẫn CityFlow; thêm nhiều parity/count-pattern formulas. Đừng đổi chúng thành việc làm mãi để tránh test phương pháp.

**Nếu target full optimized-starvation theorem chưa đóng:** không lờ đi. Đây là nghĩa vụ mở riêng ở WP1. Có thể đưa paper với restricted-information/noisy repair result nếu claim hạ đúng; không nói toàn bộ headline A đã transfer.

**Nếu learned traffic vẫn không có nesting price:** main result có thể là điều kiện một priority đủ và data-efficient learning của nó, với repair là exception handling. Không nên tiếp tục dựng benchmark nhân tạo để biến “mọi ranking đều thất bại” thành headline thực nghiệm.

**Nếu direct conditioned head dominates:** bỏ lời hứa runtime advantage. Đánh giá còn training-data efficiency, interpretability/certificate value hay theoretical contribution đủ mạnh không. Nếu không có khác biệt quan trọng nào, dừng việc claim đây là một MARL method paper mạnh; đó là kết luận nghiên cứu, không phải lỗi trình bày.

## 12. Bốn hành động kế tiếp, theo đúng thứ tự

1. WP0: sửa semantic/provenance errors và chốt joint/global information contract.
2. WP1: formalize estimated-score bridge và noisy two-world repair; đồng thời chỉ rõ Γ_f>0 optimized-allocation bridge chưa có.
3. WP3–WP4: train một genuine communication-consuming actor rồi thu joint subset pilot có strong direct head; không chạy lại full heuristic sweep chỉ để tăng số bảng.
4. Dựa trên pilot, triển khai WP2/WP5 active evidence + bounded repair, rồi WP6 final matched evaluation.

Tóm tắt trạng thái: **đã có một hướng thống nhất, một phần mathematics khá cụ thể, hạ tầng communication và diagnostic thật. Chưa có complete learned method hay evidence đủ để gọi paper MARL đã tới đích.** Kế hoạch cũ thiếu bridge tới information-feasible algorithm, joint evaluation, valid confidence, và strong budget-conditioned baseline. File này bổ sung những nghĩa vụ đó với tiêu chí kiểm, không hứa chúng đã xong.

## 13. Family chung cụ thể cho A+B+C — bổ sung quan trọng để tránh ghép cơ học

Đây là **construction mới đề xuất trong lượt brainstorm này**, với derivation trên giấy. Chưa có file Lean, chưa compile, chưa có empirical result. Chỉ dùng nó làm witness và kiểm tra tính tương thích của A/B/C trong WP1–WP2; không lấy một construction bốn packet làm bằng chứng rằng paper đã đủ novelty. Two-world Gaussian ở §7.3 là warm-up arbitrary-payoff, không thay thế communication realization.

### 13.1 Team game và observation model

Hai decision agents cùng phải xuất bit X, X uniform; team nhận 1 khi cả hai đúng. Bốn packet sources M0,M1,M2,M3. Hai decision agents thấy đúng các packet đã broadcast, không thấy bí mật riêng của sources. Có thể pad packets tới cùng số bits để unit-cost budget là thật.

- M0 là một noisy copy của X với accuracy 1/2+a.
- Có ba edges 12,13,23 giữa sources 1,2,3. World w chỉ định đúng một bad edge.
- Với mỗi edge e, chọn độc lập one-time pad U_e. Source ở đầu thấp giữ U_e; source đầu cao giữ U_e XOR Z_e. Mỗi source giữ hai shares ứng với hai edges của nó.
- Nếu e good, Z_e=X XOR E, với một noise bit E chung, P(E=1)=1/2-h. Nếu e bad, Z_e là independent fair bit. Tất cả pads độc lập với X,E và noise của M0.
- 0<a<h<1/2 tại instance chính. Model rộng hơn cho a qua zero để frozen singleton decision có actual alternatives; không bỏ những alternatives đó khỏi model khi định nghĩa surrogate game.

Khi một packet trong M1..M3 được đọc, các pads che toàn bộ X. Hai packets i,j cho phép XOR shares của edge ij. Hai agents dùng cùng deterministic decoder nên joint reward bằng correctness của bit chung.

Cần proof rằng unused shares không tiết lộ thêm X. Với một singleton hoặc bad pair, mask symmetry cho independent-of-X; với good pair, observation về X đúng là noisy parity. Đây là bước realization phải formalize, không được gán bảng payoff rồi gọi đó là communication.

### 13.2 Value table cho budgets 1 và 2

Fix cùng một decoder profile: nghe M0 thì dùng bit ấy, nghe một shared pair thì XOR đúng edge, singleton khác thì cùng đoán 0. Decoder không được retrain/flip M0 khi world thay đổi. Tại 0<a<h các rules này cũng optimal trên subsets đang xét; ở alternative a<0 ta vẫn đánh giá fixed decoder. Trên cùng game, fixed-decoder value tại các subsets liên quan là

\[
\begin{array}{c|c}
S&f_w(S)\\\hline
\{0\}&1/2+a\\
\{i\},\ i\in\{1,2,3\}&1/2\\
\{0,i\}&1/2+a\\
\{i,j\},\ ij\ne w&1/2+h\\
\{i,j\},\ ij=w&1/2.
\end{array}
\]

Vì vậy optimum ở k=1 là {0}; optimum ở k=2 là hai good pairs, không chứa 0. Nonnesting là consequence của observed team decision value. Known-world oracle được dùng chỉ để define geometry, không làm runtime input.

Với fixed world, oracle best deterministic universal ranking có worst-budget regret

\[
 V_{\rm det}^{(0)}=\min\{a,h-a\}.
\]

Best randomized pre-budget law, budget chọn trước random draw, có

\[
 V_{\rm rand}^{(0)}=\frac{a(h-a)}h>0.
\]

Derivation: x=P(first packet=0); budget-1 regret=a(1−x), budget-2 regret≥(h−a)x. Cân bằng cho x=a/h. Attainment: trộn một order bắt đầu bằng 0 với một order bắt đầu bằng một good pair đã biết đối với oracle. Không claim attainment ấy implementable khi world chưa biết.

Một replacement đủ cho oracle. Thậm chí fixed prefix template π=(0,1,2,3) có P1={0}, P2={0,1}; từ P2 đổi 0 sang 2 hoặc 3. Vì chỉ một edge bad, ít nhất một trong {1,2},{1,3} là good. k=1 giữ nguyên, k=2 sửa tối đa một lần. Do đó oracle V^(1)=0.

Đây dùng C/Structural thật, không bê parity formula sang traffic.

### 13.3 B: common repair trước exact world identification

Giữ template trên. Hai reachable high-value repairs là S12 và S13. Với tolerance ε<h−a (suy ra ε<h), acceptable sets tại k=2 là:

- world w=12: chỉ S13;
- world w=13: chỉ S12;
- world w=23: cả S12 và S13.

Giao cả ba rỗng. Nhưng {w=13,w=23} có common answer S12; {w=12,w=23} có common answer S13. Một learner có thể biết đủ để repair dù chưa biết exact bad edge. Đây là overlapping-answer structure phát sinh từ game và legal recourse.

Không phải pairwise-meet/global-empty example: hai worlds 12 và 13 ở đây đã incompatible. Nếu cần higher-order obstruction, phải tăng construction; không gọi ba worlds này là proof cho higher-order obstruction.

### 13.4 A: surrogate optimization thật, Γ_f dương

Menu calibration được chốt là Q={q0,q1,q2,q3,q12,q13,q23}: singleton evaluations và các pair trong {1,2,3}. Không bao gồm q0i; chúng là bản sao về reward distribution của q0 và nếu thêm vào phải gộp vào cùng proxy-informative group. Mỗi query là một independent simulator trial đánh giá decoder tương ứng; learner chỉ nhận reward bit, trả phí một trial. Có supervised target X trong evaluator, không tiết lộ cho deployed actors. Đây là chi phí calibration/data acquisition; không gọi là wireless sensing ở runtime.

Surrogate chỉ chứng nhận singleton winner (budget 1), nên phải phân biệt a>0 với a<0. Query M0 cho Bernoulli(1/2+a); singleton queries khác luôn Bernoulli(1/2). Các pair-evaluation kernels ĐƯỢC PHÉP trong menu trên phụ thuộc w,h nhưng không phụ thuộc a.

Với α_q là design weights trên calibration queries và d_Ber là Bernoulli KL:

\[
 J_f(\alpha)=\alpha_0\,d_{\rm Ber}(1/2+a,1/2),\qquad
 \Gamma_f=d_{\rm Ber}(1/2+a,1/2)>0.
\]

Đây lấy inf qua strict alternatives a'<0 và limit a'↑0; cần viết proof continuity/realizability. Do đó normalized sacrifice s(α)=1−α0. Mọi exact optimum chỉ đo M0; mọi design có sacrifice≤β dành tổng mass≤β cho interaction queries. Cả ba bad-edge worlds có cùng law trên M0 và singleton measurements: optimizer tốt nhất cho surrogate thực sự bỏ đói evidence cần repair budget 2.

Đây là một positive-Γ_f optimized-starvation bridge mới có thể prove, thay vì chỉ tự giả sử “proxy bỏ qua pairs”. Proxy có mục đích thật là calibration cho budget-1 decision, nhưng sai khi được dùng làm acquisition objective cho cả budget range.

### 13.5 Statistical target và scope

Hai incompatible worlds 12 và 13 đổi mean của S12/S13 giữa 1/2 và 1/2+h. KL informative query ≤

\[
 K(h)=\max\{d_{\rm Ber}(1/2+h,1/2),\ d_{\rm Ber}(1/2,1/2+h)\}.
\]

Trên 0<h≤h0<1/2, K(h) có order h². Muốn chọn ε-acceptable repair với error≤δ trong cả hai worlds, stopped change of measure buộc

\[
 E N_{\rm inf}(\tau)\ge\frac{\operatorname{kl}(1-\delta,\delta)}{K(h)}.
\]

Nếu aggregate expected acquisition sacrifice≤β, nghĩa là E N_non0(τ)≤β Eτ, suy lower

\[
 E\tau\ge\frac{\operatorname{kl}(1-\delta,\delta)}{\beta K(h)}.
\]

Candidate matching upper khi a/h nằm trong một compact subinterval của (0,1): allocate queries cho M0 và S12/S13, dừng khi biết một reachable pair có success > threshold giữa 1/2 và 1/2+h. Padded fixed-sample schedule có thể enforce β bằng counts. Đích là Θ(β⁻¹h⁻² log(1/δ)) với constants explicit theo a/h,h0; không tuyên bố exact characteristic constant hay uniform unbounded stopping đã có.

Nếu corrective pair measurements tăng chỉ O(√t), Jensen như §7.3 cho quadratic-log lower. Upper đạt linear-log với fixed informative fraction. Đây nối A→B→C trên **cùng packet game**, không ba independent examples.

Tại β=0, không thể uniform-correctly chọn repair. Tại R=0 và fixed template, geometry vẫn chặn dù có unlimited measurements. Tại R=1 và β>0, có cả quyền sửa và evidence để sửa. Đó là signature của hình N×R×acquisition-budget đề xuất.

### 13.6 Vì sao vẫn chưa được gọi “đã có novelty theorem”

XOR secret sharing, Bernoulli testing, minimax mixture và sequential change of measure đều là machinery cũ. Phần cần claim và so literature là **joint separation of structural revision power and the surrogate-fidelity cost of learning an acceptable revision across budgets**, kèm learned-MARL method có đúng costs.

**Đính chính sau phản biện:** ghép XOR/secret sharing với Bernoulli testing không tự tạo methodological novelty. Separation có thể là đóng góp nếu đúng, sắc và khác prior, nhưng finite witness này chưa xác lập điều đó. Không ưu tiên dựng thêm toy chỉ để có một hình separation. Ưu tiên dùng general nesting/interaction results hiện có, xác định chính xác law mới còn thiếu, và kiểm learned traffic có nhu cầu cấu trúc đó hay chỉ có score error. Worker chỉ nên hoàn thiện value table, no-leakage observation law, Γ_f, lower/upper của witness trong phạm vi phục vụ claim đã chốt; đối chiếu equivalent prior trước khi nâng thành headline. Không claim tôi vừa chứng minh một published-quality theorem chỉ từ sketch. Nhưng đây đã là một mathematical target có states/messages/decoders/queries/constants cụ thể, đủ để bắt đầu làm và kiểm phản ví dụ, không còn “ghép các assets theo cảm giác”.

### 13.7 Kiểm tra finite construction đã thực hiện trong lượt này

Đã viết `research/marl_budget/proposed_joint_game/exact_check.py` và chạy bằng Python standard library/Fraction. `exact_check.json` ghi source SHA256, 9 positive-parameter instances (3 cặp a,h × 3 worlds), các negative-a alternatives và 1.209 assertions. Kiểm trực tiếp latent observation law, value table, independence của singleton/bad-pair observations khỏi X, Bayes optimality ở positive-a instances, mọi 24 rankings, dual lower certificate cho randomized price và mixture attainment, cùng oracle R=1.

Ví dụ a=1/8,h=1/4: singleton tốt nhất value=5/8; good pair=3/4; deterministic universal price=1/8; randomized price=1/16; one-replacement oracle price=0. Source hash artifact khớp checker khi kiểm lại.

Đây là **exact finite validation của construction mới**, không phải proof mọi real parameters, không phải Lean gate, không chứng minh noisy stopping law và không phải kết quả traffic/MARL training. Worker có một executable specification để formalize, thay vì bắt đầu lại từ lời đề xuất.
