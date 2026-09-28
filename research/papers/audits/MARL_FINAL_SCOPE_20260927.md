# Hướng cuối cùng: Learning When to Revise Communication Priorities in Budgeted MARL

Quyết định nghiên cứu ngày 27/09/2026. Đây là phạm vi thực hiện, không phải tuyên bố đã có theorem mới hoàn chỉnh, novelty được chứng nhận hay kết quả MARL. Tài liệu này ưu tiên hơn các nhánh mở rộng trong proposal dài trước đó; không thay đổi ledger A/B/C.

## 1. Một câu hỏi

Khi các agent đã học cần phối hợp dưới bandwidth thay đổi, khi nào một communication priority dùng được cho mọi budget, khi nào cần thay một số message, và phải mua bao nhiêu dữ liệu tương tác để chọn được một cách sửa đủ tốt?

Ứng dụng chính: các intersection agents điều khiển đèn giao thông trong CityFlow đang chạy. Học actor và selector thật; không lấy max-pressure diagnostic làm MARL result. Main architecture dự kiến là infrastructure broadcast với budget chung để có một objective tập message cho joint action. Đây là lựa chọn triển khai thuộc lớp bài toán SchedNet, không có credit novelty. Adapter phải reuse thông tin/caches và byte accounting của environment hiện tại. Không loại bỏ diagnostic per-receiver.

Nhu cầu chuẩn bị priority trước grant là một giả thuyết hệ thống phải kiểm: rank có thể được chuẩn bị trước; budget đến trong một cửa sổ chọn message có deadline. Đo toàn bộ compute, kể cả phần chuẩn bị. Baseline budget-conditioned selection biết k cùng thời điểm, được cùng precomputation/cache và deadline; không bị bắt dùng ranking. Không có lợi ích thực thì bỏ claim runtime advantage, không sửa benchmark cho thuận lợi.

## 2. Câu chuyện khoa học

1. Giá trị phối hợp nằm ở tập message và controller sử dụng tập đó. Importance score từng message có thể bỏ lỡ tương tác.
2. Một score order kém không chứng minh mọi order đều kém. Đo riêng hai loại lỗi này.
3. Revision mở thêm các tập khả thi, nhưng biết có tập tốt không có nghĩa learner biết chọn tập nào.
4. Học các tương tác cần phân giải lựa chọn sửa; dừng calibration khi đã biết một cách sửa đủ tốt. Không bắt buộc reconstruct toàn bảng giá trị.
5. Khi triển khai, giữ priority hoặc sửa bằng model đã học, rồi gửi message và điều khiển. Không gọi simulator oracle để quyết định live action.

A là hạn chế của acquisition theo proxy và chi phí học evidence còn thiếu. B là acceptable repairs và dừng học khi đã đủ quyết định. C là priority commitment, budgets và quyền revision. D6/Functional nối interactions với loss. Bảy paper cũ khác dùng làm công cụ có instantiation, không tạo bảy đóng góp độc lập trong abstract.

## 3. Object và nghĩa vụ toán

Trong một calibration round, đóng băng actor profile và continuation rule. Với context z được selector phép biết, define f_theta,z(S) là expected team value khi chỉ tập S được truyền trước joint action. Phải nêu conditional observation law; full state chỉ ở training/evaluator. Controller cố định có thể cho f nonmonotone; không gọi nó Bayes-optimal value of information. Nếu claim cho optimal decoder, phải chứng minh realization phù hợp và monotonicity khi được bỏ qua thông tin.

Cho P_k(pi) là prefix k của priority pi và

    F_R(pi,k) = {S : |S|=k, |S \ P_k(pi)| <= R}.

Định nghĩa geometric loss tại context/world cố định:

    G_R(pi,k) = max_{|T|=k} f(T) - max_{S in F_R(pi,k)} f(S).

Một theorem cho pi cố định không tự là lower bound cho mọi priority. Nếu dùng min_pi max_k, phải chứng minh lower bound đồng thời cho mọi pi. Randomized max-E và E-max phải tách riêng. Multiple optima được xét qua toàn argmax; theorem distance_regret_lower hiện có không mắc lỗi đó vì distance loss có optimum duy nhất.

### T1 — Khi nào priority đủ, và quyền revision mua được gì?

Đã có source: LeanMarlSubsetFrontierV1, LeanMarlNestingDegreeGeneralV1. Giữ coefficient 2 delta cho subset decision value, không bê coefficient delta của D6 compression loss.

Cần đóng: learned-score error, actual search error, observation/actor realization; certificate dùng interaction upper bound hợp lệ. Chưa có upper bound thì chỉ ghi diagnostic. Không cần giải exact worst-case nesting degree để paper này hoàn thành.

Với true singleton gains sai không quá u, local interaction <= delta, top-k P theo estimated gains và d_k là khoảng cách đến optimum gần P nhất, mục tiêu dẫn xuất là

    regret <= 2(delta+u)(d_k-R)_+ + 2 eps_f + nu + zeta,

trong đó eps_f là uniform value error, nu là optimization error trên candidate family và zeta là coverage gap từ candidate family tới toàn F_R. Đây là target có điều kiện, chưa là theorem Lean mới trong lượt này. Không được giấu zeta bằng tên “one-swap oracle”, hoặc dùng TD loss làm eps_f.

### T2 — Chi phí học một acceptable revision

Với model class và query laws cụ thể, acceptable output là một reachable set có regret <= epsilon. Confidence event phải chứa true model; dừng khi một output acceptable cho mọi model còn plausible. Nếu cần guarantee mọi budget, output là một bảng repair theo budget và confidence/cost phải tính đồng thời.

Chốt luật giữa N (calibration samples), R (legal revisions), epsilon và confidence alpha trên một lớp model được phát biểu rõ, có lower và constructive upper trên cùng query access. Muốn gọi là bridge A, phải chứng minh proxy-optimal hoặc near-optimal acquisition thực sự hạn chế mass của informative queries, không nhận điều đó làm giả thiết rồi gọi là kết luận.

Phần machinery confidence/change-of-measure/multiple answers đã có prior; contribution cần nằm ở dependence vào reachable-repair geometry và budget commitment. XOR/Bernoulli hiện có chỉ là witness để kiểm model consistency, không đủ một mình để tuyên bố law tổng quát hay novelty.

Không thêm arbitrary m-patterns, full general MARL convergence hay một simulator khác. Nếu T2 chỉ lặp một generic testing lemma mà không cho kết quả đặc thù có ý nghĩa, phải nói scientific contribution chưa đủ; không thay bằng slogan.

## 4. Algorithm được thực thi

Training/calibration:
- Train một actor profile dùng received-message masks và ages trên traffic; phân biệt own/local input với fresh unreceived payload.
- Trong từng calibration round đóng băng actor. Học conditional set values và score từ simulator rollouts; cập nhật allocation để đo những candidate interactions còn làm lựa chọn repair không xác định.
- Controlled track dùng confidence hợp lệ. Neural track đánh giá held-out prediction/decision errors, không giả định confidence hữu hạn mẫu từ ensemble variance.
- Khi actor cập nhật, các certificate cũ chỉ được dùng lại nếu có drift bound; nếu không refresh.

Runtime:
- Từ cached/permitted context, chuẩn bị priority.
- Nhận grant k; giữ prefix nếu có cơ sở đủ tốt, hoặc chạy bounded candidate repair với R=1,2.
- Chọn từ permitted inputs; truyền packets; agents act, simulation tiếp tục trong delay.
- Log cả precompute, selection latency, bytes, deadline misses và task outcomes. R không phải latency.

Cho neighborhood nhỏ, enumerate toàn F_R để bỏ zeta. Khi scale, candidate generator phải báo search/coverage limitation. Không có theorem bảo đảm arbitrary greedy swap tìm witness của subset_frontier.

## 5. Bằng chứng tối thiểu, trước khi mở rộng

### E1: cơ chế và thuật toán trên controlled model
- Objective phải sinh từ observations và executable actors, không gán payoff rồi gọi communication game.
- Đo geometric floor khi biết model, information error khi chưa biết model, N theo confidence và R, proxy acquisition so với interaction acquisition.
- Dùng cùng worlds, queries, budget và reward cho mọi comparator. Tách counts calibration khỏi live packets.

### E2: moving traffic, matched components
- Đóng băng cùng actor để so selectors: score ranking; ranking + search; budget-conditioned subset network; exhaustive oracle trên phần nhỏ (chỉ retrospective).
- So trên cùng traffic seeds, grant traces, information và hardware. Lưu full subset/action/value tables cho audit sample; không chỉ summary.
- Báo riêng score gap, best deterministic nesting gap, critic error và search gap. Không đọc score gap thành intrinsic nesting gap.

### E3: learned MARL đầy đủ
- Train independently, có repeated training seeds; pair evaluation scenarios, không xem nhiều states là independent training seeds.
- Baselines: SchedNet adaptation, direct budget-conditioned selector, score + matched local search; thêm communication baseline mạnh tương thích protocol. Native baseline và adaptation phải ghi riêng.
- Fixed, bursty và shifted budget distributions; held-out traffic loads/topology phù hợp scope. Control delay tiêu thụ simulation time.
- Main endpoint: team performance so với bytes và measured latency/deadline misses. Report completed/unfinished trips, queues và throughput; không che censoring trong mean travel time.
- Acquisition ablation báo calibration cost tính bằng simulator steps, same training budget; không chỉ data count khi rollout lengths khác nhau.

## 6. Bốn hình chính

1. Một scene traffic: cùng k, một score chọn sai tổ hợp, repair đổi joint action; thêm một scene no-repair để không kể mọi state đều cần sửa.
2. Controlled frontier: geometric regret theo R và learning regret theo N; đường oracle chỉ làm reference.
3. Traffic Pareto: team outcome vs bytes và selection latency. Direct budget-conditioned network là comparator bắt buộc.
4. Ablation: singleton-only / uniform interactions / decision-targeted acquisition, cùng calibration cost; báo benefits và uncertainty qua training seeds.

## 7. Tiêu chí giữ claim và điểm dừng

Paper hướng tới một law + executable algorithm + learned-MARL evaluation. Không yêu cầu mọi theorem A/B/C trở thành theorem cho neural traffic, và không bắt buộc traffic có worst-case nesting degree lớn.

Các kết quả phủ định phải giữ:
- Best ranking tốt nhưng score ranking kém: contribution thực nghiệm là học/repair score, không “mọi priority thất bại”.
- Direct budget-conditioned selector bằng hoặc tốt hơn trên tất cả performance/resource axes: không claim practical advantage của precommitment/repair. Đây là dấu hiệu phải đánh giá lại deployment premise trước khi train lớn hơn.
- Certificate luôn vacuous hoặc chỉ sampled maximum: không gọi deployable certified algorithm.
- Bridge N/R chỉ là restatement không khác prior và system không có lợi ích: không coi đã đạt đích publishable.

Không hứa acceptance hoặc zero collision. Sau khi các mục bắt buộc hoàn thành, freeze scope để viết/evaluate; không tự mở sang CARLA, Minecraft, CNN pruning hay thêm family parity.

## 8. Prior trực tiếp đã kiểm cho quyết định này

- SchedNet, ICLR 2019: https://arxiv.org/abs/1902.01554 — shared bandwidth, scheduling, encoding và actions đã có. Hệ thống broadcast không phải novelty.
- IMAC, ICML 2020: https://proceedings.mlr.press/v119/wang20i.html — bandwidth-limited learned communication/protocol/scheduling đã có. Không claim joint communication learning mới.
- Münch, Raach, de Vries, Recoverable Robust Cardinality Constrained Maximization with Commitment of a Submodular Function: https://optimization-online.org/wp-content/uploads/2025/07/main-3.pdf — đã đọc abstract, definitions 1–5 và results. Fixed-cardinality monotone submodular selection, adversarial deletions, replacement; proof machinery “commit rồi repair” là prior. Không suy paper này không có nội dung khác vì chưa đọc hết appendix.

Khoảng phân biệt cần bảo vệ là quantitative learning of acceptable revisions cho budget-dependent team-message value, cùng dữ liệu và chi phí thực thi. Việc ba source trên khác mô hình không phải chứng nhận toàn literature không có equivalent.
