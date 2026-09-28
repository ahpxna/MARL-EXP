# Paper MARL mới: kiểm proposal, recourse và vai trò A — 27/09/2026

## Verdict và phạm vi

Đối tượng là paper MARL mới, không phải audit lại Paper B. Đã đọc toàn bộ đoạn paste, bản MARL_SYNTHESIS_RESEARCH_PROPOSAL_20260926.md, các đoạn related work hiện tại của C, một số đoạn A, đường shadow update của code, metadata/raw checks của C recourse, và những nguồn primary bên dưới. Không chạy train, không compile Lean, không khẳng định đã audit toàn bộ paper/results, không dùng subagent.

Đoạn paste đúng khi cảnh báo universal ranking, limited recourse, decision-focused communication và varying bandwidth đều có prior art. Nhưng không thể kết luận novelty chỉ từ việc chưa thấy ai ghép đúng danh sách keyword. Cần một quantitative result trên team decision, một protocol không nhìn trộm payload và một lợi ích thực nghiệm so với selector budget-conditioned mạnh.

A không bị kết luận là hết giá trị. Proposal hôm trước để A optional vì nó giả định một selector/critic đã biết đánh giá tập message. Đó là cách thu hẹp phạm vi, không phải chứng minh A không cần. Nếu nghiên cứu việc học/đo các tương tác dưới chi phí, A là một câu hỏi chính.

## 1. Prior art đã kiểm và các correction

- [Unknown-capacity knapsack](https://epubs.siam.org/doi/10.1137/16M1070049): universal order đã có. Tuy nhiên items không fit bị bỏ qua; không đồng nhất với lấy đúng k phần tử đầu. Không dùng khác biệt này để claim universal ordering mới.
- [Incremental Submodular Maximization](https://arxiv.org/html/2606.28558v1), Introduction/Thm 1–2: đúng là một thứ tự cho mọi cardinality. Giả thiết monotone submodular; thuật toán 1.373 cần optimum cho từng cardinality và không được trình bày là efficient runtime method. v1 ngày 26/06/2026, không phải bắt đầu tháng 8. Team message value có complementarity không tự thuộc lớp này.
- [Chassein et al., recoverable selection](https://eprints.lancs.ac.uk/id/eprint/87346/1/paper.pdf), model ở trang 2–3: chọn p items, reveal uncertain costs, exchange tối đa k items. Đây là antecedent trực tiếp của bounded exchange, nhưng uncertainty là cost và cardinality p đã cố định.
- [Hommelsheim et al., commitment](https://link.springer.com/article/10.1007/s10107-026-02385-7): choose set, adversary deletes elements, augment while preserving survivors. Có bản preprint 2023, journal 2026. “Commitment” ở đây không phải tự do đổi mọi phần tử sau reveal. Nó chặn claim inventing two-stage recourse, không phải chứng minh model MARL đã được giải.
- [Münch et al., Acta Informatica 2026](https://link.springer.com/article/10.1007/s00236-026-00542-1): monotone submodular set, deletions, replacement of deleted members. Không đồng nhất với varying budget và unrestricted non-submodular team risk. Có predecessor IWOCA 2025.
- [Goal-oriented communication/MBDP](https://kclpure.kcl.ac.uk/portal/en/publications/goal-oriented-semantic-communication-in-bandwidth-constrained-mar/): xác nhận ICC Workshops 2025, alternating communication/navigation policies dưới bandwidth constraints. Bản extended PDF được index với LLM-BDP, nhưng mở full PDF thất bại; chưa coi claim TVT và toàn bộ no-retraining protocol là đã kiểm đầy đủ.
- [BAMAS, AAAI 2026](https://ojs.aaai.org/index.php/AAAI/article/download/40226/44187): chọn LLM pool và topology dưới token/cost budget. Adjacent MAS; không phải physical multi-agent traffic control nên không nhất thiết là baseline chạy chung.
- [Don't Fire Together](https://pubmed.ncbi.nlm.nih.gov/42590554/): primary abstract/metadata xác nhận Sensors 2026, frozen learned policy, communication scheduling và staleness. Full PMC gặp challenge. Không claim toàn bộ theorem của bài đã được đọc; generic staleness-aware scheduling không mới.

Các prior MARL CASEC/MUTE/SchedNet/NDQ đã nằm trong memo trước, không được quảng cáo lại action-preserving pruning là mới. Lượt này không deep-read lại tất cả chúng.

### Quan trọng: corpus hiện tại đã biết một phần các collision

`paper_c.tex:204–250` đã cite incremental optimization, regret-minimizing permutation, recoverable selection và commitment-under-deletion, đồng thời phân biệt chúng. Vì vậy câu “dự án bỏ sót hoàn toàn” không đúng với C hiện tại. Bản MARL proposal cần đối thoại kỹ hơn với chúng; đây là thiếu của proposal, không phải phát hiện rằng C mất novelty.

## 2. Đối tượng toán cần chốt

Fix một public context z. E là finite message/source set, K là finite set budgets. ell_z(S) là team loss kỳ vọng của một decoder class có quyền truy cập đã xác định, không phải loss được nhìn thấy miễn phí trong execution. Assume minima attained. Có thể dùng Bayes risk của finite team game; phải phân biệt với uniform delta-correctness của B.

P_k(pi) = prefix size k; d(S,T)=|S triangle T|/2 với |S|=|T|=k.

    ell*_z(k) = min_{|S|=k} ell_z(S)
    g_R(pi,k) = min_{|S|=k, d(S,P_k(pi))<=R} ell_z(S) - ell*_z(k)
    V_rand(R) = min_{P on rankings} max_{k in K} E_P[g_R(pi,k)]

Đây là ORACLE planning object: selector biết ell_z. Runtime phải thay min bằng một policy dùng đúng public history/paid data. Reference dùng cùng decoder/information capabilities. Nếu có band/availability/topology constraints, đưa vào mọi feasible set và reference, không bỏ trong một vế.

Budget fixed before random draw gives max E. Budget chosen adversarially after observing ranking gives E max. Hai bài toán khác nhau. C đã có đúng distinction này; moving bandwidth traces cần mô tả cụ thể thay vì gọi tất cả là ex-post.

## 3. R* trong paste: đúng nhưng chưa phải contribution chính

Đặt O_k=argmin_{|S|=k} ell_z(S), không có thêm constraints:

    R* = min_pi max_k min_{S in O_k} d(P_k(pi),S).

Mỗi replacement bỏ đúng một item và thêm một item. Nếu mọi intermediate size-k set đều legal thì d là số replacements cần và đủ. Do đó V_det(R)=0 iff R>=R*. Với finite sets và nonnegative regret, V_rand(R)=0 cũng tương đương: expectation zero ở mỗi k buộc mọi ranking trong support đạt zero ở mọi k; lấy một ranking trong support.

Điều này KHÔNG có nghĩa randomization vô dụng ở positive regret. Toy p=1/4 có V_det(0)=1/4 nhưng V_rand(0)=1/8; V_rand(1)=0. R* chỉ trả lời exact recovery threshold, không xác định cả frontier.

Nếu có marginal bands bắt buộc randomization, intermediate topology constraints, item costs khác nhau, hay selector không biết ell, characterization trên chưa tự áp dụng. Khoảng cách tới oracle optimum cũng không cho một efficient algorithm tìm optimum.

Một family gần-optimal O_k(epsilon) cho deterministic epsilon-threshold tương tự, nhưng không được mang nguyên worst-case set distance sang randomized expected-epsilon frontier. Cùng toy cho thấy randomization có thể đạt average guarantee dù mỗi realized ranking vi phạm ở một budget.

### Submodularity không được giả định

Trong toy, v(S)=ell(empty)-ell(S). v({2})=v({3})=0, v({2,3})=1/2. Nó vi phạm submodularity. Vì vậy các guarantees cho monotone submodular incremental maximization không tự xử lý toy này. Synergy/XOR bản thân là kiến thức cũ; một counterexample này chưa đủ novelty.

### Đích mạnh hơn một định nghĩa R*

Cần một class của thực sự joint-decision problems và matching quantitative bounds cho V_rand(R), theo một tham số interaction hoặc cấu trúc information có thể kiểm/ước lượng được. Không định nghĩa tham số bằng chính frontier rồi gọi là characterization.

Một certificate hữu ích: tìm weights lambda_k>=0, sum lambda=1 và gamma sao cho với mọi ranking pi,

    sum_k lambda_k g_R(pi,k) >= gamma.

Khi đó V_rand(R)>=gamma. Cho một ranking mixture và legal repair đạt upper cùng mức. Đây là finite minimax/LP machinery cổ điển; contribution phải là certificate và attainment cụ thể trên decision family, không phải LP duality.

## 4. Hai chỗ proposal đang ngầm giả định quá nhiều

### R ít không đồng nghĩa latency thấp

Tìm best one-swap bằng brute force cần k(m-k) candidate evaluations. Một amortized budget-conditioned network có thể chọn subset bằng một forward pass. Cần đo wall-clock, compute, bytes của coordination protocol, không suy cheap từ R=1.

Deadline/ranking caching là justification có thể kiểm, không phải fact. Direct budget-conditioned selector, same model trained across budgets, là baseline bắt buộc. Nếu nó nhanh và tốt hơn thì bỏ claim recourse algorithm hữu ích; structural theorem vẫn có thể tồn tại.

### Geometry known không đồng nghĩa repair executable

Recipient không được đọc all candidate payloads rồi mới quyết định message nào được tính chi phí. Bộ chọn cần dùng public/local cached history, hoặc trả phí cho metadata/query. “Messages có sẵn ở sender” không làm message content hoặc set utility miễn phí ở receiver.

Trong `models/core_behavior.py:473–524`, shadow update vẫn đọc current obs_j, action_j và relation features của mọi candidate; chỉ full encoder bị cắt theo core. Đây là compute-saving code, không tự chứng minh communication saving. Không gọi đây là lỗi của compute-only experiment; cần adapter đúng information contract cho communication track.

## 5. Đưa A trở lại mà không ghép hình thức

Phân biệt:

- C: repair một SET sau budget reveal (R replacements).
- A: repair một MEASUREMENT ALLOCATION đang tối ưu surrogate nhưng thiếu decision information (sacrifice beta).

Hai repair không cùng resource; không nhân hai constants hoặc đem Gaussian bound sang actor bằng analogy.

Đề xuất tích hợp: learned agents nhận team reward; một selector học set-level coordination effects từ paid interaction probes/ablation data. Trước reveal có acquisition policy và ranking dựa vào permitted history. Sau reveal, bounded repair policy chọn set và agents thực hiện joint action qua implementable coordination protocol. Trong runtime moving traffic, acquisition/revision tiêu thụ thời gian và observations bị stale.

A cung cấp câu hỏi: proxy-driven data acquisition có bỏ đói interactions quyết định tốt/xấu của repair không, và phải sacrifice bao nhiêu proxy objective để nhận đủ thông tin? B cung cấp acceptable repair/actions và obstructions; C cung cấp geometry của reachable sets. Không claim A đã chứng minh câu trả lời cho hệ này.

### Bridge error đơn giản, đã dẫn trên giấy (không phải novelty mới)

Với fixed pi,k và F_R={S:|S|=k,d(S,P_k(pi))<=R}, giả sử trên đúng event/calibration domain:

    sup_{S in F_R} |ell(S)-ell_hat(S)| <= epsilon
    ell_hat(S_hat) <= min_{S in F_R} ell_hat(S)+nu.

Chọn S_R optimal thật trong F_R, thì

    ell(S_hat) <= ell_hat(S_hat)+epsilon
               <= ell_hat(S_R)+nu+epsilon
               <= ell(S_R)+nu+2epsilon.

Suy ra:

    ell(S_hat)-ell*_k <= g_R(pi,k)+2epsilon+nu.

Nếu model stale với uniform loss drift D, thay epsilon bằng epsilon+D. Nếu bound chỉ high-probability, phải đưa failure event vào expected loss với boundedness thích hợp. Không suy uniform epsilon từ empirical TD loss. Nếu ranking cũng học từ data, cần kiểm estimation error trên union của sets có thể được chọn, không chỉ prefix đã thấy trong training.

Đây tách structural commitment cost, information/estimation cost và search error. Nó chưa là trajectory return bound; phải nối actual induced actions và occupancy như T2 của memo trước.

### Mathematical target có vai trò A/B/C thật

Cho world theta, budget k, ranking pi và tolerance epsilon, định nghĩa acceptable repairs

    A_{epsilon,k,pi,R}(theta)
      = {S in F_R(pi,k): ell_theta(S) <= ell*_{theta,k}+epsilon}.

Trước hết kiểm mỗi world có acceptable repair (C). Sau đó xác định khi uncertainty còn lại có common implementable answer (B). Cuối cùng định nghĩa observation channel của interaction probes và phân tích surrogate-guided versus repaired allocation (A).

Đích là một finite cooperative decision family nơi (i) còn structural loss khi R nhỏ, (ii) khi geometry đã cho phép repair thì vẫn có statistical cost để tìm nó, và (iii) một allocation/decoder đạt upper phù hợp. Constants/general stopped rates/multiple-answer optimality phải được chứng minh lại theo đúng assumptions; không nhận việc ghép tên các theorem là proof.

## 6. Experiments và các evidence đang có

C artifact `research/unified_20260919/paperC_budget_recourse.json` ghi NUMERICAL (HiGHS), typed model. Producer hash khớp script hiện tại. Các rows/checks hỗ trợ C families, không có learned controller/team reward nên không phải MARL validation. Lượt này đọc metadata/checks và rows đại diện; chưa audit lại toàn solver, không tuyên bố whole artifact certified.

`research/new_chains_v2/ACTUAL_EXPERIMENT_RUN_CHECK.md` tự ghi PLUMBING_SMOKE_ONLY, scientific gates false và tiny pretraining. Không dùng nó để tuyên bố trained MARL đã thắng baselines.

Nên chốt bốn experiments liên kết, không mở nhiều simulator:

1. Finite team game: brute-force subset loss, exact randomized ranking/repair LP; sweeps interaction/noise và R. Test cả regime ranking đủ tốt và regime synergy phá nesting.
2. Paid acquisition: giữ fixed frozen actor/decoder rồi thay acquisition policy (proxy, uniform, task-aware, proposed repair); cùng measurement count. Đo coverage của decision-critical interactions và actual repair regret. Đây là test A, không chỉ attention heatmap.
3. Runtime selection: cùng trained representation, so universal prefix, R=1/2 repair, budget-conditioned selector, per-budget oracle nhỏ; report post-reveal latency thực tế.
4. Moving multi-agent traffic: ít nhất hai learned decision agents; physics chạy trong query/communication delay; unseen scenes/budget traces, collision/progress/timeout/return và bytes/latency/staleness. Full information chỉ là labeled diagnostic. WAIT vô hạn không tính task success.

Không cho privileged state dùng trong centralized training rò vào execution. Labels từ simulator để train/evaluate không được trở thành online oracle selector. Giữ raw per-episode outcomes, training seeds độc lập, source/config hashes; no pooling hides worst regimes.

Ablation acquisition x revision phải có đủ: proxy/no-repair; improved-acquisition/no-repair; proxy/repair; improved-acquisition/repair. Giữ controller và tuning resources matched. Nếu proposed repair cần all payloads miễn phí hoặc rất nhiều candidates, charge chúng.

## 7. Thứ tự hoàn thành và stop rules

1. Freeze information/timing/cost contract: pre-budget context, ai biết gì, khi nào k reveal, query/bytes/compute/metadata costs, R tính trước transmission hay temporal edits.
2. Formalize oracle finite-team frontier, giữ randomized max E và adversarial-after-draw E max riêng; R* là auxiliary fact.
3. Vượt toy ba message: prove một useful structural class với lower certificate và attainment/approximation; không chỉ nhiều examples rời rạc.
4. Discharge decision/control bridge: actual joint action, decoder/inference error, distribution shift, learned critic uncertainty.
5. Nếu muốn A là central, instantiate paid interaction channel và prove acquisition lower/upper trên cùng finite game. Nếu chưa làm được, giữ A như application/hypothesis được đánh giá, không tuyên bố toàn bộ A transfer.
6. Implement execution-feasible rank/repair và direct budget-conditioned comparator. Đo latency trước training lớn.
7. Controlled mechanism tests rồi moving MARL, cùng protocol và thống kê.
8. Chốt novelty ở new quantitative decision/acquisition–recourse result và benefit với strong comparators. Không claim first universal ranking, first recourse, first budget-aware communication, hoặc first staleness-aware scheduling.

Nếu direct selector dominance còn nguyên: hạ bỏ method advantage, giữ structural finding hoặc chuyển trọng tâm sang acquisition (A). Nếu real traffic không có meaningful nonnested gap: báo kết quả âm, không sửa benchmark chỉ để bảo vệ câu chuyện. Không có requirement rằng mọi paper con phải thành theorem trong MARL manuscript; nhưng A không được lặng lẽ coi là đã tích hợp khi chưa có paid acquisition object.

## Gợi ý positioning

Nghiên cứu chi phí thông tin và giới hạn sửa cấu trúc phối hợp khi resource budget chỉ được biết muộn: interactions có thể khiến một ranking tối ưu theo proxy vừa học thiếu evidence vừa không phù hợp ở nhiều budgets; quantify phần loss do geometry, phần do thiếu measurements và khả năng khôi phục bằng acquisition/revision có chi phí. Moving traffic kiểm tính thực dụng của mechanism. Đây là TARGET/PROPOSAL, không phải kết quả MARL đã có hoặc chứng nhận novelty.


## 8. Nếu cần một object chung đặt A vào trung tâm

Đề xuất cho finite controlled team game, chưa phải theorem đã có:

    mathfrak_V(N,R) = inf_{A in Pi(N,R)} sup_theta max_k
        E_theta[ell_theta(S_k) - ell*_{theta,k}].

Pi(N,R): learner được nhiều nhất N paid interaction observations trước reveal; cả query policy và ranking dùng permitted history; budget k reveal sau đó; final set cách prefix tương ứng tối đa R replacements; decoder/team actions phải executable. Đây là fixed-sample planning definition. Nếu chuyển sang expected stopping cost hoặc moving state, định nghĩa lớp policy riêng, không tráo chúng.

- N đo chi phí HỌC đủ thông tin (A/B).
- R đo quyền SỬA tập phối hợp (C).
- ell là actual team-decision risk với decoder class đã chốt (Functional/Support).
- D6 có thể cho một regime score-based selection đủ, khi bound interaction được instantiate.

Chỉ định nghĩa bề mặt này không tạo novelty. Mathematical target đáng làm là một family không tầm thường có matching bounds cho cả phần geometric obstruction và phần statistical identification-of-repair. Ví dụ R đã đủ để một oracle sửa tốt, nhưng measurement allocation theo proxy vẫn không phân biệt được các worlds đòi hỏi những repairs khác nhau; một repaired acquisition policy giải được với cost định lượng. Tránh oracle nhìn true theta hoặc all untransmitted payloads.

Một câu hỏi hẹp hơn, đủ để bắt đầu: fix public ranking và R, dùng acceptable repairs ở mục 5. Nếu các tập này nonempty và channel thỏa assumptions của B, define decision-resolution order s*(R,epsilon). Khi R tăng, acceptable sets lớn hơn nên obstruction family chỉ có thể thu hẹp; resolution requirement không tăng trong cùng fixed task/channel. Áp order law cần cả information upper/lower comparability. Chứng minh s* thật sự đổi trên một family derived from joint loss, thay vì tự gán labels, mới cho một nội dung concrete. Sau đó mới cho ranking học từ dữ liệu và tính giá proxy-starvation của A.

Đây là phương án nâng paper, không phải bắt buộc thêm cả general dynamic-MARL theorem trước khi có experiment. Nếu scope này quá lớn, giữ C-led MARL và A độc lập; nói rõ lựa chọn thay vì tuyên bố cả ba đã được tích hợp.
