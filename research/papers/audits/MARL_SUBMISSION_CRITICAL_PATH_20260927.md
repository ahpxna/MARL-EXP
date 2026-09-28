# Đường găng tới bản MARL có thể gửi — 27/09/2026

Tài liệu thực thi cho worker, theo yêu cầu ưu tiên tiến độ nộp bài. Không phải ledger, không thay `MARL_FINAL_SCOPE`, không chứng nhận novelty hay acceptance. Không mở thêm simulator hoặc hướng lý thuyết. Các việc bảo trì công cụ không được chặn actor và thí nghiệm.

## 1. Quyết định phạm vi ngay

**Câu hỏi của paper:** khi budget truyền tin thay đổi, priority đã chuẩn bị có đủ không, một số ít replacement sửa được bao nhiêu tổn thất phối hợp, và cần học tương tác nào để chọn được repair hữu ích?

**Gói đóng góp tối thiểu để gửi:**
1. T1: bound cho output hợp lệ của selector có sai số score/evaluator/search.
2. T2: một kết quả calibration có scope chính xác, cùng một query model ở hai chiều. Hiện là needle class, không được viết thành universal MARL sample-complexity law.
3. Selector chạy được với evaluator học được và actor MARL thật.
4. Moving-traffic evaluation có đối thủ trực tiếp budget-conditioned, acquisition ablation, chi phí truyền và thời gian chọn thực đo.

Không chờ đóng log|Amb|, pairwise-interaction class, all-budget calibration hay actor-drift theorem tổng quát mới bắt đầu train. Những việc đó là mở rộng. Tuy nhiên nếu muốn giữ các claim tương ứng trong abstract thì chúng lại trở thành bắt buộc; không được vừa bỏ proof vừa giữ claim.

## 2. Audit: điều gì báo cáo đúng, điều gì cần đổi cách hiểu?

Đã đọc nội dung T1/T2, scope, các diagnostic CityFlow một/hai hop, environment/counterfactual access/rollout, artifact liên quan và statement B/C được nhắc. Đây không phải lượt đọc lại toàn bộ corpus A/B/C.

### T1

- Bound của `LeanMarlEstimatedRevisionV1.deployed_regret` có thật trong source, với bốn loại sai số riêng. Bản source T1 đã có local olean mới hơn source; trạng thái đó không tự xác nhận một release hoàn chỉnh.
- **Thiếu về ý nghĩa thuật toán:** `deployed_regret` không yêu cầu mọi S trong C phải nằm trong F_R. Bound đúng nhưng riêng statement đó không chứng minh output hợp lệ về budget/revision.
- Đã thêm `LeanMarlRevisionAuditBridgeV1.deployed_regret_feasible`: giữ theorem gốc và thêm điều kiện C ⊆ F_R, trả cả `Reach` và regret bound. Worker compile module mới này; không cần viết lại T1.
- Hai transfer lemma mới: nếu |f−fhat|≤e trên mọi subset thì ScoreLocal chuyển với +2e và LocalInteraction chuyển với +4e. Có thể dùng cho sai số bảng giá trị hoặc drift đã được chặn. **Đây chưa phải chứng minh xác suất của event sai số.**
- Với learned traffic, không có uniform upper confidence bound thì bỏ claim “certified no-repair” khỏi thuật toán neural. Vẫn dùng và đo learned selector; theorem T1 giữ dưới giả thiết được công bố. Không lấy ensemble variance hoặc sampled maximum làm certificate.

### T2

- Source `LeanMarlRepairCalibrationV1` đã viết lower/upper trên cùng Gaussian needle channel. Trong ảnh chụp audit chưa tìm thấy olean của T2 và không thấy tiến trình compile T2 đang chạy; “đang compile nền” không phải trạng thái được xác nhận tại thời điểm kiểm.
- Lower đang cho horizon hữu hạn, expected non-dummy-query cost tại null world. Upper là fixed schedule + decoder. Đừng mô tả thành optimal expected stopping time của mọi adaptive unbounded protocol.
- Gains và beta biết trước; `hSep` bỏ một lớp near-tie; singleton-invisibility của needle cần điều kiện kích thước needle ít nhất 2.
- **R tăng không tự làm bài toán học khó hơn.** Trong construction hiện tại, family world/benchmark reachable cũng thay đổi theo R. Với cùng model class và cùng yêu cầu accuracy, thêm quyền sửa có thể bị bỏ qua nên không thể tự nó làm infimum sample cost tăng. Viết “worst-case cost over the specified R-dependent class”, hoặc cố định class rồi phân tích trade-off đúng.
- `choose(k,R) choose(m−k,R)` là shell count dưới các điều kiện tham số đã ghi; không phải hàm tăng theo R trên mọi miền. Ngoài miền khả thi count có thể bằng 0; với fixed beta/gamma còn có điều kiện gamma R < beta−epsilon.
- `geometric_floor` và calibration upper chưa mặc nhiên ghép thành một theorem cùng world class: upper chỉ xét reachable needle. Khi so global optimum, tách
  `global regret = geometric floor + regret within reachable family`.
  Nếu theorem phát biểu comparator là k-set, ghi rõ cardinality đó.
- Log|Amb| gap và near-tie extension được giữ là limitation cho lần nộp này. Không gọi bounds là matching in every parameter. Có thể gọi cùng power beta^-2 và dependence tuyến tính vào số ambiguous repairs, sai khác logarithmic factor theo cardinality, trong đúng miền.

### Thí nghiệm hiện có

- Diagnostic có giá trị, không phải chưa có dữ liệu nào: bản một hop 1,180 records; hai hop 708 records. Hash của các artifact đã đối chiếu với producer/environment tại lúc audit.
- Nhưng đó là **oracle diagnostic với max-pressure cố định**, chưa phải learned-MARL evaluation.
- f_i(S) hiện chỉ đổi message của agent i; các agent khác dùng full communication. Nó không đo global broadcast set S đồng thời tác động lên toàn đội.
- Một self-check “no deployed action used oracle data” ở diagnostic một hop được gán `ok=True`; không phải assertion kiểm access log. Kết quả toán khác không vì thế tự động sai, nhưng check này không chứng minh không leak.
- Artifact chưa lưu đầy đủ bảng mask→joint action→value để tái tính decomposition.
- Hai hop có 124/708 score gaps ở R=0, 23/708 ở R=1; best deterministic nesting gap có 5/708 ở R=0 và 0 ở R=1. **Đừng kể “mọi priority đều kém” từ score gap.** Không có intrinsic gap ở R=1 cũng là kết quả hữu ích, không cần chế scenario để bắt nó dương.
- Rollout diagnostic giữ joint action trong horizon. Không gọi đó là return của learned closed-loop continuation.

## 3. Đã làm ngay để worker tiến tiếp

### Selector: `models/marl_revision_selector.py`

`reachable_sets(ranking,k,R)` liệt kê mỗi k-set hợp lệ đúng một lần, prefix trước, sau đó tăng số replacement. Hỗ trợ R=0,1,2 và lớn hơn; IDs không cần liên tục.

`select_revision(..., evaluate=...)` thực hiện exact argmax trên toàn F_R, tie ưu tiên ít replacement, log enumeration/evaluation/total selection seconds. Nếu cap không đủ thì fail trước khi evaluate; không tự chuyển sang greedy rồi vẫn báo coverage gap bằng 0. Evaluator phải cố định trong một lần gọi (eval mode, tắt dropout).

- Với bảng fhat xác định: search gap nu=0, coverage gap zeta=0.
- Sai số giữa fhat và return thật chưa được giải quyết bằng hàm này.
- Hàm không biết runtime được phép đọc thông tin gì; worker phải truyền evaluator chỉ dùng permitted context.
- Hàm chưa tính bytes, precompute time, deadline misses hoặc simulation delay. Những mục đó thuộc runner.

Ví dụ nối neural evaluator:

```python
result = select_revision(
    ranking, k, R,
    evaluate=lambda selected: frozen_set_critic(permitted_context, selected),
    max_candidates=4096,
)
# Budget legality is guaranteed for this result. Transmission and actor execution
# must still go through the environment's permitted protocol.
```

`complete_table_bounds` trả delta_U, eta_U và u_U có điều kiện trên simultaneous coverage của **toàn bảng**. Nó từ chối bảng thiếu subset. Dùng cho controlled experiment, không dùng để đổi tên neural prediction error thành chứng nhận.

Bốn test đã PASS, gồm exhaustive đối chiếu tập hợp độc lập cho m≤8, mọi k và R=0..3; interaction cần hai replacement; cap/NaN/invalid inputs; và bounds cho tương tác bậc cao với bảng bị thiếu bị từ chối. Chạy:

```bash
cd /Users/phanan/cig-amf-main
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest tests.test_marl_revision_selector -v
```

### Toán: `LeanMarlRevisionAuditBridgeV1.lean`

Đã viết ba proof nêu trên. **Chưa compile trong lượt này.** Worker compile sau, sửa elaboration nếu cần; nội dung cần giữ là legality và deterministic transfer, không được thêm uniform coverage làm kết luận khi chưa có giả thiết xác suất.

### Bản thảo B, sửa lỗi ngắn

Đã sửa câu trong supplement rằng eta~h “erases the advantage”. Thế eta=c h vào eta²h⁴+h⁶ vẫn cho order h⁶; exponent 4 là regime eta>0 cố định. Không đưa theorem ungated mới vào main paper. Editor compiler chưa dựng được supplement vì standalone compiler không thấy `preamble.tex`; đây là giới hạn project-file của compiler, không phải kiểm chứng PDF thành công.

## 4. Đường găng thực thi — làm đúng thứ tự này

### Bước 1 — khóa protocol và sửa phép đo chung, không chờ train lớn

File bắt đầu: `envs/external/cityflow_budgeted.py`, adapter hops, hai `DIAG_cityflow_set_objective*.py`. Viết runner v2 riêng, giữ nguyên producer cũ và JSON cũ.

1. Chốt S là **tập sender broadcast toàn mạng**; receiver i chỉ nhận S∩N(i). Nếu vẫn dùng per-receiver budget thì phải gọi đó là model khác, không đọc kết quả thành global-bandwidth result.
2. Cho mọi agent cùng dùng restricted view để sinh joint action. Lưu f_joint(S), không chỉ f_i(S) khi các agent khác full comm.
3. Chốt selector được biết context z nào trước grant: topology, cache, age, public grant history, permitted local summaries. Scheduler không được đọc queues/payload mới của mọi sender trước khi trả tiền truyền. Nếu có control bids/score broadcast thì tính bytes của chúng và cho baselines cùng quyền.
4. Lưu raw subset masks, sender IDs, actions, rewards, actor hash, continuation rule, traffic/budget seed, horizon và clocks.
5. Đánh dấu đoạn oracle evaluation tách khỏi live selection. Snapshot access counters ngay trước/sau live rank→select→act; assertion phải fail nếu oracle API được gọi trong đoạn đó. Oracle calls của diagnostic vẫn được phép ở đoạn riêng.
6. Chạy một scene nhỏ để kiểm cơ chế. Không đợi hàng nghìn records mới phát hiện object sai.

**Done:** một bảng f_joint tái tính được, cùng một deployment step không đọc oracle. Đây là WP0 v2, không phải main MARL figure.

### Bước 2 — train một actor có message thật rồi đóng băng cho E2

Repo có `models/policy_value.py` và `scripts/run_external_training.py` để reuse network/training loop. Runner cũ không tự là runner cho protocol budget mới; phải nối input và communication access cho đúng. `models/kprefix_net.py` có ranking head nhưng không thay thế budget-conditioned subset baseline.

1. Actor input: own observation + received-message mask/payload + age/cache; unavailable fresh payload không được lấp bằng full state. Mask phải phân biệt missing với giá trị zero.
2. Train với budget/mask diversity đã chốt để actor học sử dụng message và chịu missingness. CTDE critic có thể thấy training state; actor runtime không được thấy.
3. Save checkpoint và input schema. Kiểm full/no communication, shuffle message, stale message: actor có thực sự dùng channel hay không. Đây là diagnostic, không đòi phương pháp mới thắng ở bước này.
4. Đóng băng **cùng checkpoint** khi train/compare selectors; giá trị f không được đổi giữa các selector.
5. Nếu cập nhật actor, tạo calibration round mới, refresh evaluator. Cách này tránh phải chờ theorem drift của neural actor trước khi chạy paper.

**Done:** một learned actor checkpoint, evaluation có thể replay, không phải max-pressure. Một seed đủ kiểm wiring; không đủ kết luận thắng baseline.

### Bước 3 — evaluator, selector và comparator mạnh trên cùng actor

1. Training-only rollout/counterfactual labels để học fhat(z,S); cùng continuation policy và horizon giữa mọi S. Tách calibration/test bằng episode/scenario, không random các states gần nhau vào hai phía.
2. Score w và set evaluator dùng cùng permitted runtime context. Nếu thiếu thông tin thì target là conditional expected value given z; không train dùng full state rồi đòi deploy từ cache như thể hai inputs giống nhau.
3. Dùng selector đã thêm để chạy R=0,1,2. Với m lớn hơn cap, giảm kích thước diagnostic hoặc ghi restricted-candidate method riêng; không gọi exact enum.
4. Baselines tối thiểu:
   - score priority prefix;
   - score + matched local search với cùng evaluator/candidate/compute;
   - **direct budget-conditioned selector**, nhận k và cùng context, cùng quyền precompute;
   - retrospective exhaustive oracle ở subset panel nhỏ, chỉ làm reference;
   - random và full/no communication làm reference phụ.
5. Báo decomposition: score-prefix error; best deterministic priority gap; evaluator-induced decision error; search/coverage gap. Đừng dùng correlation fhat/f làm proxy duy nhất cho chọn repair đúng.
6. Đo wall-clock precompute và post-grant selection riêng; tổng compute cũng báo. Tính communication bytes, control overhead, deadline misses. R chỉ là số replacement, không phải latency.
7. Trong moving traffic, delay có ý nghĩa phải tiêu thụ simulation time hoặc dùng fixed declared delay model được kiểm; không chỉ in milliseconds cạnh simulator đang pause.

**Done:** paired pilot trên vài seeds/scenarios cho biết repair có ích và cái giá latency của nó. Đây là phép thử quyết định trước khi train nhiều seeds.

**Nếu budget-conditioned selector bằng hoặc tốt hơn mọi trục:** bỏ claim practical superiority của precommitted priority; không cấp thêm privilege cho phương pháp mình. Nếu không còn lợi ích deployment hay scientific mechanism nào rõ, chưa có cơ sở nói MARL paper đã sẵn sàng. Deadline không biến negative result thành win.

### Bước 4 — E1 calibration: giữ gọn nhưng kiểm đúng câu chuyện A+B

1. Giữ needle class của T2 với điều kiện đã nêu. Compute Amb và các shell theo đúng miền, biết g/beta, finite horizon; không gọi generic CityFlow theorem.
2. So singleton/proxy allocation, uniform repair measurements và acquisition chọn ambiguity ảnh hưởng acceptable repair, cùng query costs.
3. Đo probability output acceptable và số calibration queries; ghép R bằng hai đồ thị: geometric floor theo R và extra estimation regret theo N. Không suy causal claim “R tăng làm data khó” từ changing world class.
4. Các Gaussian repeated observations thuộc controlled model. CityFlow rollouts có bounded/stochastic/correlated returns khác; tách scope.
5. Nếu muốn thực thi certified finite-table version, với L queried sets, n independent bounded-return samples/set trong interval độ rộng B, dùng radius `B sqrt(log(2L/alpha)/(2n))` cho simultaneous table event. Với Gaussian variance σ² đã biết, radius `σ sqrt(2 log(2L/alpha)/n)`. Đây là fixed-sample construction, không tái dùng nguyên xi khi optional stopping. Full table cho delta_U đòi L=2^m trừ khi có structural upper bound khác.
6. Không làm full-table calibration nếu nó làm main method chậm mà paper không claim runtime certificate. Neural evaluation có thể empirical; phải ghi rõ.

**Done:** một plot calibration có acceptable-repair criterion, matched cost và uncertainty. Nếu chỉ có zero-allocation failure thì mô tả đúng như vậy; near-optimal optimized starvation của A chưa tự được chuyển sang MARL.

### Bước 5 — main learned-MARL runs và acquisition ablation

Chỉ mở sau pilot E2 xác nhận đáng chạy. Dùng nhiều independent training seeds, paired evaluation traffic/budget seeds; khởi đầu 5 training seeds nếu tài nguyên cho phép, report mọi seed và tăng khi khoảng tin cậy chưa phân biệt được hiệu ứng có ý nghĩa. Không xem hàng nghìn correlated states là hàng nghìn independent replications.

- Một CityFlow setup chính, thêm traffic-load shift hoặc budget-distribution shift được chốt trước. Không cần CARLA/Minecraft hoặc simulator thứ hai.
- Fixed, bursty và shifted grant traces. So SchedNet adaptation, direct budget-conditioned selection, score+matched search và phương pháp mình dưới cùng protocol/budget.
- Main outcomes: team return, queues, throughput, completed/unfinished trips; travel time chỉ trên completed trips phải đi cùng unfinished fraction.
- Pareto: quality versus bytes, quality versus measured selection latency/deadline misses. Report cả precompute và calibration simulator steps.
- Acquisition ablation: singleton-only / uniform interaction / decision-targeted, cùng simulator-step budget, cùng actor/evaluator architecture và tuning allowance.
- Báo held-out acceptable-repair rate, value/decision error và failure cases; không chỉ training loss.

**Done:** dữ liệu main result + ablation + paired uncertainty. Chỉ giữ headline có dữ liệu đỡ.

### Bước 6 — gom bản gửi và dừng mở rộng

Bốn figure đủ để kể toàn câu chuyện:
1. Traffic scene: cùng k, priority chọn tổ hợp gây quyết định kém, R=1 sửa joint action; kèm scene không cần sửa.
2. Controlled: geometric floor theo R và learned regret theo calibration N. Bound/measurement phân loại rõ.
3. Moving traffic Pareto: performance–bytes và performance–latency; direct budget-conditioned bắt buộc hiện trên hình.
4. Acquisition ablation + uncertainty qua training seeds, fixed resource budget.

Bản thảo theo mạch: problem/protocol → revision geometry T1 → learning acceptable repair T2 → executable method → controlled calibration → moving-traffic results → limits. T1/T2 proof checking gom thành một lần kiểm cuối trước khi gắn nhãn formal; không dùng vòng compile nhỏ làm lý do trì hoãn experiments.

Không cần neural MARL convergence theorem. Không cần claim exact traffic sample complexity. Không cần thêm family parity, arbitrary m-patterns, every-budget confidence hay shared-pair theory cho lần gửi này.

## 5. Việc khó giao worker, phân loại có chặn nộp không

| Việc | Cách làm ngắn nhất đúng scope | Chặn bản gửi? |
|---|---|---|
| Actor/observation realization T1 | Define f từ đúng actor + channel + continuation; instantiate finite-set theorem. Không chứng minh mọi abstract f đều là optimal-decoder value. | Có |
| Valid output F_R | Dùng wrapper mới và enum selector mới; mapping message IDs→Fin m. | Có |
| Learned actor và evaluator | Train actor, freeze từng round, calibrate evaluator, runtime chỉ permitted context. | Có |
| δ_U từ dữ liệu | Controlled full-table simultaneous CI; neural giữ conditional theorem nếu không có coverage. | Chặn claim certified, không chặn empirical method |
| Actor drift | Freeze/refresh; drift theorem chung chuyển sang future work. Transfer +2e/+4e đã viết. | Không với frozen rounds |
| T2 compile | Sửa module hiện có, giữ nguyên assumptions/rates; không nhân tiện mở theorem mới. | Có nếu claim formal T2 |
| T2 log cardinality gap | Ghi lower/upper đúng; adaptive sequential test là hướng sau, cần đổi benchmark horizon cho nhất quán. | Không |
| Near-tie/multiple answers | Giữ hSep trong theorem; empirical acceptable set dùng epsilon regret, không ép identify T. | Không cho restricted theorem |
| Shared-pair interactions | Sau nộp: phi(S)=(s_i s_j), model linear in pair parameters, KL=(phi(S)·(theta−lambda))²/(2σ²); thông tin query chia sẻ, không nhân số Amb máy móc. | Không |
| Uniform all-budget repair table | Sau nộp: shared confidence event, joint output table, reuse measurements; không cộng chi phí từng budget như độc lập. | Không |
| Near-optimal proxy starvation | Nếu giữ claim optimized acquisition: cần Γ_proxy>0, all/near optimizers và mass bound trên informative queries. Zero-sampling example không đủ. | Chặn claim A mạnh, không bắt buộc cho revision algorithm paper |
| Optimal decoder monotonicity | Chỉ cần nếu đổi object sang decoder tối ưu có quyền ignore messages. Fixed actor có thể nonmonotone. | Không trong scope hiện tại |

## 6. Dừng ở đâu là thật sự đủ để gửi?

Đủ để chuẩn bị gửi khi: statement T1/T2 chính xác và đã kiểm; actor/selector chạy bằng information hợp lệ; so sánh E2/E3 có kết quả với baselines mạnh cùng resource; controlled result và traffic ablation nối được learning interactions→chosen repairs→team outcomes; bốn figure và uncertainty tái tạo được. Khi đó khóa scope và hoàn thiện bản gửi.

**Chưa thể nói đã publishable chỉ từ 12 theorem T1 hoặc việc T2 compile.** Phần đang thiếu nặng nhất là bằng chứng learned-MARL và lợi ích so với direct budget-conditioned selector. Cũng không cần đóng mọi ô future work mới được gửi.
