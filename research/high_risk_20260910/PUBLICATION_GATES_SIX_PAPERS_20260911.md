# Sáu paper: novelty, evidence hiện tại và điều kiện để nộp

Ngày kiểm: 2026-09-11. Đây là đánh giá trên các claim, source và artifact được chỉ ra dưới đây; không phải bảo đảm chấp nhận, hay chứng nhận đã tìm hết mọi công trình. Danh sách công việc áp dụng cho **những claim muốn giữ trong bản nộp**. Một nhánh mở rộng có thể bỏ khỏi claim thay vì phải giải xong toàn bộ chương trình nghiên cứu. Không cần formalize toàn bộ corpus để nộp một paper toán, nhưng mọi định lý được quảng bá là Lean-verified phải có audit đúng statement và dependency closure tái lập.

## Quyết định hiện tại

**Chưa đủ căn cứ để gọi cả sáu bài là sẵn sàng nộp.** Structural gần một gói lý thuyết độc lập nhất; D6 có lõi static đáng theo và hướng reference mạnh, nhưng claim adaptive đầy đủ vẫn mở. Functional đã có evidence mới tốt sau sửa generator; baseline và đóng góp thuật toán vẫn chưa đủ. Support cần luật kết hợp geometry với truy vấn; Query còn thiếu chân runtime tự nhiên; MASTER cần đóng góp định lượng riêng ngoài việc ghép contract.

| Paper | Phần đã có giá trị | Việc đang chặn claim mạnh nhất | Lựa chọn phạm vi khả thi |
|---|---|---|---|
| Structural | Upper không balance và lower cùng bậc theo epsilon; staircase mọi r | So sánh đúng với incremental/K-adaptability; làm rõ tồn tại so với thuật toán | Paper về minimum menu of rankings cho normalized cancellation geometry |
| D6 | Sharp margin ở corner, same-Q game, cyclic/epoch/revalidation; nghiên cứu reference | Actual general-reference bridge và WLOG; adaptive total regret, expected Gamma | Nộp lõi static trước, hoặc chờ đủ chuỗi adaptive nếu đó là headline |
| Functional | V4 random labels/extrema vẫn khoảng 2.485x so uniform | Chưa chạy C_lucb; chưa có kết quả mới về full alternative/unknown extrema | Paper về cost of changing Top-C + allocator dựa trên geometry đó |
| Support | Witness thật, obstruction order, cardinality membership laws, concrete contract sound | Obstruction size không quyết định query cost; cần thông số joint và luật mới | Decision-safe acquisition dưới physical query restrictions |
| Query | Synthetic identifiability floor thật, positive controls | Natural panel vẫn chưa có evidence nondegenerate đã xác minh | Minimal representation repair trên tác vụ thực; nếu không có, gộp Support |
| MASTER | Một contract cụ thể sound đã prove; composition và evidence pipeline | Giá trị gia tăng riêng; runtime nhỏ đang thua exact solve | Priced completion/reuse với lower–upper cost và break-even thực |

## Những cập nhật của bạn đã được kiểm

### Functional v4: đã có kết quả, không còn phải chờ hai job

Hai file `research/confirm_ieee_20260911/functional_v4_ieee10seed_cellv1.json` và `functional_v4_shift50_cellv1.json` hoàn tất. Mỗi file có 1.000 world, 7 policy, horizon 131.072. Bộ kiểm mới tính lại mọi median và tỷ lệ từ rows; kiểm SHA artifact với manifest; dựng lại **đủ 2.000 world** từ RNG để đối chiếu fingerprint. Tất cả khớp.

| Variant | Run chính: certify | Median N | Shift50: certify | Median N |
|---|---:|---:|---:|---:|
| C_anytime | 74,9% | 29.884 | 76,0% | 29.820 |
| C_known_sigma — diagnostic | 75,0% | 29.108 | 76,0% | 29.364 |
| C_extrema_oracle — diagnostic | 75,7% | 26.428 | 76,9% | 26.228 |
| C_pilot | 72,5% | 39.413 | 73,3% | 38.989 |
| C_shrink | 72,8% | 39.637 | 73,1% | 38.685 |
| C_split | 69,3% | 60.201 | 69,3% | 61.953 |
| uniform | 60,5% | 74.252 | 59,7% | 74.348 |

Run chính: ratio of medians = 2,484674. Conditional trên 605 cặp cùng certify: 601 thắng, 4 thua; thêm 144 chỉ anytime, 0 chỉ uniform. Median paired ratio = 2,229656; CI distribution-free 95% [2,154386; 2,289314], ranks 278/328 của n=605. Hai estimand khác nhau, không thay thế cho nhau. Shift50: 596 thắng/1 thua trong 597 cùng certify, thêm 163 chỉ anytime. Không gọi là domination. Hai panel không phải 2.000 world độc lập hoàn toàn vì dùng cùng seeds và chia sẻ bước sinh capacity.

Zero-information accuracy là 8,9% và 9,2%, phù hợp mục tiêu 1/10; cả mười Top-2 sets đều xuất hiện. Fixed-label confound đã được gỡ. Không false-safe trong hai panel là observation, không phải chứng minh risk bằng zero; không xem 14.000 policy runs có common random numbers là 14.000 phép thử độc lập.

Bốn điều chưa được đóng bởi kết quả này:

1. **C_lucb có trong source hiện tại nhưng không có trong hai artifact.** Vẫn thiếu so sánh cùng thông tin với comparator này. Nó là baseline adapted từ nguyên lý confidence-bound; chưa được đồng nhất với implementation/theorem của Huang 2017.
2. **Shift50 không phải drift trong thời gian.** `_draw_world` resample extrema trước khi sinh streams. Không có change-point sau pilot, không có learner từng khoá extrema cũ. Với 5 relation, Python `round(.5*5)=2`: chỉ redraw 2/5 rows. Đây là panel static khác. Vì redraw có thể chọn lại vị trí cũ, cũng không đảm bảo mọi row được chọn đổi cặp extrema.
3. **Seed đúng không tự chứng minh confirmatory.** `admissibility_record` hiện trả CONFIRMATORY chỉ vì tuple seeds khớp; không kiểm source/config/endpoint đóng băng trước run. Label correction hậu nghiệm không cung cấp lịch sử đóng băng còn thiếu. Dữ liệu vẫn dùng được làm empirical evidence; mức prospective confirmation cần chứng từ riêng.
4. **Source fingerprint đang được lấy lúc ghi kết quả.** `write_artifact_with_provenance` gọi `source_fingerprint()` sau `run()`. Nếu source thay đổi khi job chạy, hash này không chứng minh bản code Python đã load lúc khởi chạy. Cần snapshot/source hash đầu run và bản config đầy đủ. Không được ghép C_lucb mới vào narrative của run cũ.

Lưu ý v3: fixed true labels tạo shortcut cho predictor biết generator; nó **không logic-guarantee** mọi noisy policy sẽ luôn chọn đúng. Câu “false_safe phần nào guaranteed” cần đổi thành “panel không kiểm được lỗi do nhãn thật thay đổi”. Và dù RNG mới giữ world/noise prefixes giữa horizons, Bonferroni và pilot budget còn phụ thuộc H: so sánh horizon vẫn là hai procedure được ghép dữ liệu, không phải cùng một stopping trajectory kéo dài.

### Lean và audit

`LeanBinaryPinskerV1` hiện có olean mới hơn source, log không lỗi, bốn print axioms chuẩn. Bản sửa EventuallyEq xử lý đúng lỗi khai triển log toàn cục. Statement hiện là **binary Pinsker với p,q thuộc (0,1)**. Chưa vì thế mà có theorem Pinsker cho mọi probability measure, endpoints, hay KL của adaptive transcript. `two_point_error_weak` cho floor khi binary KL nhỏ; gọi “đúng bậc” chỉ hợp lý trong regime small-KL đã quy đổi, không tự có cả dependence log(1/delta).

`LeanD6AcquisitionBenchmarkV1` cũng đã audit sạch sáu tên: discovery-only excess khi oracle đo cùng cyclic design, và toàn deployment cost khi oracle miễn phí. Đây là accounting identities đã đóng; không tự là full expected-Gamma theorem.

Lỗi binder tại `LeanD6BernoulliSlopeV1.slope_at_A` được sửa trong lượt này bằng `(Finset.ne_of_mem_erase hb) h`, tránh `subst` xoá j. Module A compile exit 0, 13 audit chuẩn. Module B cần thêm `rw [← hBdef]` để rewrite đúng tên block; sau sửa compile exit 0, một audit chuẩn. Hai olean mới hơn source. Đây là slopes thật đã đóng, chưa là toàn general-reference minimax bridge. Lưu ý docstring cũ của module B nói hai số mũ khác nhau cùng khớp khi |A|=k, |B|=k−1 là không chính xác; statement đã prove dùng đúng |A|+|B|−1=2k−2.

Census trước sửa slope: 321 source, 159 module có audit riêng sạch, 2 có log không in axioms, 156 không log riêng (143 có olean, **13 không olean**), 4 có compile errors. Trong failed logs có 3 module in sorryAx. Điều đó không có nghĩa một theorem đã compile thành công với sorryAx; Lean có thể tạo recovery proof sau lỗi. Nó cũng làm câu “toàn corpus 0 sorryAx” sai nếu đang mô tả toàn bộ log. Số cuối cập nhật trong `publication_snapshot_20260911.json` sau compile.

Audit hạ nguồn phủ **declarations thực sự được dùng**, theo closure phụ thuộc; không phủ mọi theorem chỉ vì cùng import một file. 55 module trong manifest là selected gate, không phải toàn corpus. Regex cũ `[^']+` còn bỏ sót declaration có dấu prime trong tên, như `hasDerivAt_gap'`; bộ kiểm snapshot mới đã sửa parser và kiểm đủ bốn tên Pinsker. Vì vậy không dùng số audit print từ parser cũ như census đầy đủ. “25 closed/4 open” là đánh giá semantic viết tay, không phải kết luận tự sinh từ compilation. Tự glob MODULES giúp inventory nhưng không thay thế claim-to-theorem mapping. Không cần bắt mọi file thử nghiệm thất bại phải compile để chứng nhận một paper đã cô lập dependency closure.

## Công việc chung phải làm cho mỗi bản nộp

- [ ] G01 — Chốt một central claim, phạm vi model và scientific question. Ghi rõ world/reference/support/noise, learner biết gì, oracle biết gì, query nào hợp lệ, một đơn vị chi phí là gì.
- [ ] G02 — Lập bảng claim → statement → assumptions → proof/artifact → limitation. Đặc biệt tách hLaw đã được dựng với hCoverage/hFuture/geometry còn là giả thiết.
- [ ] G03 — Viết so sánh theorem-level với prior gần nhất: input, output, objective, additive/multiplicative, exact/epsilon, Bayesian/minimax, static/adaptive. Một ví dụ nằm ngoài giả thiết của prior chỉ chứng minh không áp trực tiếp, chưa chứng minh novelty.
- [ ] G04 — Có human-readable proof của mỗi headline; phân biệt theorem, conjecture, exact finite certificate và Monte Carlo. Numerical LP optimum không tự thành universal optimum.
- [ ] G05 — Nếu quảng bá Lean verification: release một pinned build của dependency closure cần dùng, sạch từ môi trường mới; audit đúng headline; hash source/toolchain/manifest. Lưu exit code của Lean, tránh lấy exit của tee. Không cần clean toàn bộ các bản thử đã bỏ.
- [ ] G06 — Chốt experiment/model/baseline/endpoint trước dữ liệu holdout mới; lưu immutable source + config lúc launch, actual arguments, seeds, raw outcomes, failures và thời điểm. Không thay nhãn thành confirmatory chỉ từ seeds.
- [ ] G07 — Kiểm generator/oracle/units độc lập: random labels, không lộ answer, đúng physical constraints, đúng reference và noise. Nếu normalization/data filter đổi, ghi rõ population bị đổi.
- [ ] G08 — Baseline có cùng thông tin, cùng admissible queries, cùng confidence và budget accounting. Tách oracle diagnostic; thêm baseline literature áp dụng được hoặc giải thích reduction và assumption khác.
- [ ] G09 — Báo query cost, compute, precomputation, certification, fallback và memory nếu có claim thực dụng. Không chỉ so stopping sample count rồi kết luận wall-clock nhanh.
- [ ] G10 — Báo đúng uncertainty: unit là world/seed phù hợp với design; conditional paired analysis ghi điều kiện; xử lý censoring, ties, multiplicity, failures; zero errors là empirical observation.
- [ ] G11 — Một result có một paper sở hữu chính; paper khác dùng/cite. Nếu Support, Query, MASTER chỉ diễn đạt lại cùng obstruction/contract thì gộp thay vì giữ số lượng sáu bằng mọi giá.
- [ ] G12 — Bản nộp phải tự đọc được: notation thống nhất, assumptions trước theorem, algorithm pseudocode, related-work comparison, limitations, release instructions và bằng chứng tương ứng. Không dùng chuỗi addendum lịch sử thay manuscript.
- [ ] G13 — Chọn venue theo loại đóng góp rồi kiểm scope, format, anonymity, code/data/ethics/disclosure và chính sách overlap. IEEE chỉ là tổ chức, không phải một tiêu chuẩn novelty duy nhất. Tier B/C trong protocol hiện cần adapter thật; không phải bắt buộc cho mọi paper lý thuyết nếu bỏ claim MARL/crossroad.

## Structural: giữ hướng fixed-epsilon normalized menu law

Điểm phân biệt nên là số ranking cần để mọi budget có một prefix epsilon-good dưới radius có cancellation. Incremental maximization đã có một ordering phục vụ mọi cardinality; K-adaptability đã hỏi số policy đủ. Structural cần bảo vệ **minimum menu size + normalized additive error + concrete nonmonotone geometry**. [Bernstein et al.](https://link.springer.com/article/10.1007/s10107-020-01576-0), [Bienkowski et al.](https://arxiv.org/abs/2606.28558), [Kurtz](https://link.springer.com/article/10.1007/s10107-026-02329-1).

- [ ] S01 — Viết một main theorem upper/lower cùng model và cùng normalizer B=Σ osc(f_i)/2. Nêu B>0, xử lý B=0 và miền epsilon. Upper không balance đã có: không làm lại.
- [ ] S02 — Nêu đúng quantifier lower: với mỗi epsilon chọn family đủ lớn; không nói một fixed normalized epsilon vẫn có unbounded menu khi upper độc lập width đã chặn nó.
- [ ] S03 — Dùng full staircase curve đã prove; không quay lại finite census hay “thiếu factor 2”. Tách sharp threshold của staircase với constant tối ưu của universal upper.
- [ ] S04 — Tách existence và computation. Upper đang dùng exact-ranking/optimization tại anchors. Hoặc công bố oracle algorithm và số oracle calls, hoặc chứng minh solver hiệu quả trên subclass có ý nghĩa. Nếu claim polynomial thì cần proof thời gian/encoding.
- [ ] S05 — Viết reduction/assumption comparison với Kurtz đúng: integer budgets không là convex uncertainty set; floor-prefix extension còn discontinuous/nonconcave. Không kết luận chỉ concavity là giả thiết hỏng. Kiểm cả continuity, feasible policy class và meaning của approximation.
- [ ] S06 — Nếu giữ empirical algorithm claim: exact optimum nhỏ, K=1, greedy/incremental phù hợp, menu heuristic; cùng epsilon và costs; runtime kèm query/oracle calls.
- [ ] S07 — Kiểm normalized fixed-epsilon trên unbalanced radii, cancellation và mức precision khác nhau. Không suy universal precision theorem từ vài scalar points. Thí nghiệm minh họa không thay lower theorem.
- [ ] S08 — Chỉ rõ luật menu giúp quyết định gì: reuse qua budget/latency, hoặc impossibility của một ranking. Nếu không có deployment thì giữ paper lý thuyết và giải thích ý nghĩa mô hình.

Mở rộng có giá trị nhưng không bắt buộc: constant sharp hơn; instance-dependent covering law chặt hơn Θ(1/epsilon); algorithm không cần exact anchors. Đây là tăng độ mạnh, không phải lý do phải trì hoãn một theorem package hẹp đã hoàn chỉnh.

## Functional: full alternative khi extrema chưa biết

Huang et al. 2017 đã cho structured rewards từ micro-observations, nhưng LUCB-micro yêu cầu reward map coordinatewise monotone cùng điều kiện interval-witness. Range max−min không monotone theo raw means: nâng (0,1) thành (0.5,1) làm range giảm. Vì thế không tự coi theorem của họ đã chứng minh thuật toán hiện tại, cũng không được coi tên “functional” là mới. Unknown variance và pure-exploration games đã có framework; cần novelty trong geometry/algorithm cụ thể. [Huang 2017](https://proceedings.mlr.press/v76/huang17a.html), [Jourdan et al.](https://arxiv.org/abs/2210.00974), [Degenne et al. 2019](https://proceedings.neurips.cc/paper/2019/hash/8d1de7457fa769ece8d93a13a59c8552-Abstract.html).

- [ ] F01 — Dùng v4 làm population chính cho claim unknown Top-C; lưu v3 là restricted fixed-label/extrema diagnostic. Phần randomization đã xong, không đòi chạy lại chỉ để chứng minh điều đó.
- [ ] F02 — Chạy baseline C_lucb còn thiếu, trên cùng saved worlds/noise và confidence; công bố là adaptation đã mô tả. Trước holdout mới, kiểm code/tuning trên development seeds. Nếu thêm benchmark published khác, phải tôn trọng assumptions và accounting của nó.
- [ ] F03 — Chọn stationary hay drifting headline. Nếu stationary, bỏ diễn giải shift50 thành recovery-after-change. Nếu maintenance, cần change-point thực, train/pilot trước change, update/refetch sau change, và confidence method hợp lệ cho nonstationary data; không dùng nguyên prefix-t như iid qua change.
- [ ] F04 — Định nghĩa toàn bộ alternative set làm đổi Top-C, gồm khả năng đổi argmin/argmax, ties và epsilon-good answers. Pair-flip theorem hiện là unrestricted two-score subproblem, chưa là full problem.
- [ ] F05 — Cho known independent Gaussian cell variances, chứng minh minimum KL bằng minimum trên các region chọn extrema của hai relation. Mỗi region có các bất đẳng thức tuyến tính ép extrema và capacity crossing, nên subproblem là convex quadratic optimization. Cần proof hợp của các region đúng bằng closure alternative set, không chỉ thử numerical.
- [ ] F06 — Nếu response phải đến từ cùng F/reference/support, đưa các ràng buộc realizability vào optimization; so với free response-table relaxation. Nếu claim unknown variances, tối ưu cả nuisance variance đúng model; quadratic known-sigma cost không đủ.
- [ ] F07 — Từ oracle alternative đó, derive allocation và guarantee tương ứng; generic max-min information game không tự là novelty. Tìm explicit regime/law hoặc separation giữa fixed-extrema allocator và full-extrema allocator.
- [ ] F08 — Prove certificate validity theo đúng sampling/stopping implementation; nếu claim expected-optimal stopping thì phải chứng minh termination, tail và expected rate, không chỉ existence/safety.
- [ ] F09 — Noise model hiện có sigma theo action dùng chung qua relations. Ghi rõ ai biết cấu trúc chia sẻ này; mọi baseline phải có cùng thông tin. Nếu muốn arbitrary cell noise phải mở generator/model rồi test.
- [ ] F10 — Báo certificate curves, censored time/RMST với cutoff rõ, median và CI đúng sample size; paired conditional metrics không gọi domination. V4 có cả thắng và thua.
- [ ] F11 — Nếu residual maintenance là contribution riêng: derive hCoverage/hFuture từ measurement/drift model, cộng cost refresh/fallback; finite minimum-cost existence chưa là policy optimality.
- [ ] F12 — Sau freeze, chạy fresh heldout đủ để trả lời effect chính, heterogeneity/gap/extrema-location và scale. Không cần thêm seeds vô hạn; cần precision/power theo effect đã chọn. Cần real/sim task phù hợp nếu giữ claim ứng dụng, không nhất thiết cho một bài lý thuyết thuần.

Hướng đáng thử nhất: **luật chi phí đổi quyết định khi active extrema có thể chuyển**, kèm efficient separation oracle và allocator tương ứng. Min-over-extrema-QPs là một đường triển khai cụ thể, chưa tự chứng minh “chưa ai làm”. [Huang et al. 2018](https://www.microsoft.com/en-us/research/wp-content/uploads/2018/05/ijcai18_CPE-CS.pdf), [Dorn et al.](https://arxiv.org/abs/2503.00509), [Wang–You](https://arxiv.org/abs/2606.21889) là các so sánh bổ sung cần giữ; Wang–You giới thiệu recipe/characteristic value, không nên tự gán cho họ mọi theorem asymptotic optimality.

## Support: geometry phải đi cùng khả năng phân tách của query

Bennouna **có** combinatorial extension (Corollary 1, PDF trang 15) và noisy observations (Proposition 10, trang 52). Prop.10 là perturbation guarantee cho một query set đã sufficient, chọn trước; chưa phải luật adaptive sample complexity dưới physical membership queries. Decision regions chồng lấn cũng đã có trong DRD/HEC. [Bennouna et al.](https://arxiv.org/pdf/2602.15365), [Javdani et al.](https://arxiv.org/abs/1402.5886).

- [ ] U01 — Chốt actual support model, epsilon-safe decision set, allowed physical queries và cost; nêu learner biết toàn world set hay chỉ biết một description/oracle.
- [ ] U02 — Giữ witness selectedRadius và exact cardinality laws đã prove. Không đưa chúng lại vào danh sách chưa formalize.
- [ ] U03 — Phát biểu separation đã gợi ra: obstruction order lớn vẫn có thể chỉ cần một query. Do đó Helly/obstruction number riêng không thể là complexity parameter đầy đủ.
- [ ] U04 — Định nghĩa joint parameter dùng cả incompatibility của safe decisions và query-induced partitions/KL. Không chỉ đổi tên Bellman optimum hay generic characteristic time; cần tính được hoặc so sánh được trên một class thật.
- [ ] U05 — Prove lower và constructive upper theo parameter đó trên actual supportOsc/selectedRadius; phân biệt Bayesian expected cost với minimax worst-case cost, deterministic với randomized policy.
- [ ] U06 — Nếu noisy: transcript law, testing/decision lower bound, confidence-valid acquisition và stopping. Nếu nhiều correct answers, kiểm đúng answer-wise alternative set; không ép recovery toàn world khi chỉ cần safe decision.
- [ ] U07 — Compare exact optimal decision tree nhỏ, random/greedy, và DRD/HEC khi prior/test assumptions khớp. Baseline khác objective phải ghi rõ; 5.276 vs 9.21 random chưa đủ khẳng định cạnh tranh literature.
- [ ] U08 — Không cho free access tới support table mà lại tính chỉ membership costs. Báo chi phí feasibility/oracle, world enumeration, memory và scale.
- [ ] U09 — Test partial safety epsilon>0, correlated supports và query restrictions có ý nghĩa; giữ lower examples nhưng bổ sung nơi method có lợi, nếu claim practical.

Hướng novelty: **hai geometry có cùng obstruction order nhưng khác query separability tạo complexity khác bậc, và một luật joint khớp cả hai**. Helly links trong learning là prior để so sánh, không suy membership complexity trực tiếp. [Bousquet et al.](https://arxiv.org/abs/2005.11818).

## D6: tách static theorem package và claim adaptive đầy đủ

Generic fixed-confidence Gamma, tracking và game-based exploration đã có; fixed-budget complexity cũng có giới hạn riêng. D6 cần contribution ở legality, hidden A, growing q, reference và allocation phase, không chỉ lắp framework vào notation mới. [Garivier–Kaufmann](https://proceedings.mlr.press/v49/garivier16a.html), [Degenne 2023](https://proceedings.mlr.press/v195/degenne23a.html).

**Gói static có thể nộp mà chưa cần full adaptive Gamma:**

- [ ] D01 — Khóa definition của delta-box, margin, V và class reference. Corner point mass được phép nếu theorem chỉ cần normalized nonnegative product reference; full-support assumption phải kiểm ở downstream. Không gọi corner theorem là uniformly robust over references.
- [ ] D02 — Human proof của sharp threshold 2 và same-Q positive-margin family; corner part đã compile. Phân biệt margin min(mu,2−mu) của family cũ với margin parameter mới.
- [ ] D03 — Ghép slopes a(t),b(t),z thật, expectation và modular compensation thành equality của **cả hai response levels** cho mọi hidden A. General-reference slope modules là bước tiến, chưa tự là toàn bridge.
- [ ] D04 — Ghép actual residual oscillation/optimal retained set vào count-based game cho mọi legal query/decision. Không chỉ verify bảng reduced game.
- [ ] D05 — Prove symmetry averaging/WLOG và endpoint-action domination; rồi primal/dual certificate cho toàn class. Các exact certificate finite-grid hỗ trợ, không thay universal reduction.
- [ ] D06 — Ghi đủ domain của formula, đặc biệt sufficient condition (k−2)b≥1 và các sign/endpoint regimes trong derivation. Nếu chưa xử lý ngoài domain thì giới hạn theorem; không quảng bá full phase diagram.
- [ ] D07 — Từ finite-k formula, prove limit t=tau/k và quantitative errors/order of limits. Đường boundary dự kiến 2(1+tau)e^(−2tau)=rho cần nối từ family thật.
- [ ] D08 — Tách hai câu hỏi: F cố định rồi đổi reference, và compensated F_t thay đổi theo t để giữ cùng Q. Sweep của hai câu hỏi không thay thế nhau; full support t~1/k không là bounded-away-from-zero reference.
- [ ] D09 — Final tables/plots đối chiếu exact nhỏ, rational reduced certificates và asymptotic law; chính xác evidence class từng plot. Không cần primitive m=10/block-composition route đã bị family trực tiếp thay thế.

Cost-aware identification tự nó cũng đã có lower bound và asymptotically matching algorithm trong [Kanarios–Zhang–Ying 2024](https://arxiv.org/abs/2402.16710). Vì vậy thêm giá query vào objective chưa đủ novelty; cần luật cụ thể về reference và ambiguity.

Hướng mới mạnh nhất: **giá của thay reference để phá ambiguity**. Giữ một compensated world tại t0 cố định, query tại t1 làm A/B slope contrast thay đổi theo c(t1)−c(t0). Cần model observability/cost và matching lower–upper; hiện đó là research target, chưa theorem acquisition. Reference dependence/purification tự nó đã có trong functional ANOVA. [Borgonovo et al.](https://arxiv.org/abs/1801.05186), [Lengerich et al.](https://proceedings.mlr.press/v108/lengerich20a.html).

**Nếu giữ claim adaptive matching total regret + expected Gamma thì còn toàn bộ các mắt nối sau:**

- [ ] A01 — Một algorithm đầy đủ, cùng filtration và actual legal observations; quy định exploration, discovery, revalidation, tracking, phase handling và final output. Không dùng true A/true phase trong code learner.
- [ ] A02 — Ghép actual adaptive transcript KL, không chỉ one-query KL dưới fixed uniform adjacent-swap prior. Conditional allocation có thể phụ thuộc observations; phải giữ hoặc kiểm soát averaging phù hợp.
- [ ] A03 — Binary testing/data processing → Bayes/minimax lower bound trên đúng decision loss. Pinsker interior đã có; endpoints/singular laws/measure KL vẫn phải xử lý khi xuất hiện. Nếu muốn log(number of worlds) hoặc log(1/delta), cần lập luận multi-hypothesis hoặc sharper testing riêng.
- [ ] A04 — Discovery lower/upper khớp theo q, gap và confidence; nêu rõ small-KL regime. Weak testing floor và Pinsker chỉ là công cụ trong bước này.
- [ ] A05 — Dùng canonical path/cyclic law và epoch/revalidation results đã prove, rồi cộng đúng loss qua horizon. Không commit một Ahat có thể sai và bỏ regret đó.
- [ ] A06 — Confidence sequence cho mu/allocation trên mọi epoch: error schedule summable, ví dụ delta_s=delta/((s+1)(s+2)). Width có log s; fixed constant times sqrt(v_s log(1/delta)) ở vô hạn independent epochs không đủ. [Howard et al.](https://arxiv.org/abs/1810.08240).
- [ ] A07 — Prove estimate-to-value hoặc estimate-to-allocation stability qua phase boundaries. L1 Lipschitz theo weights không tự chặn mu→w*(mu). Nếu weights nhảy, chuyển sang direct value bound thay vì giả continuity sai.
- [ ] A08 — Nối desired weights với realized legal query counts; include forced exploration, raw budget, integer leftovers và discovery overhead. Integer theorem hiện chỉ tối ưu giữa hai block designs đã đặt tên.
- [ ] A09 — Stopping time adapted, certificate đúng actual terminal decision, a.s. termination cho full algorithm. Một stability window nhìn vào tương lai tại đầu window không phải stopping time ở thời điểm đó.
- [ ] A10 — Tail/integrability cho expected stopping cost và limsup đúng Gamma; a.s. convergence hoặc high-probability eventual correctness riêng không đủ.
- [ ] A11 — Dùng lại hai cost conventions discovery/deployment trong `LeanD6AcquisitionBenchmarkV1` đã có sáu audit sạch; ghép chúng với decision loss và comparator của main theorem. Cancellation với oracle bị ép chạy cùng cyclic design chỉ chứng minh comparator đó, không tự đạt unrestricted legal-query Gamma. Không cần prove lại sáu acquisition identities.
- [ ] A12 — Matching total regret và limit q=q(T): chỉ ra nơi discovery cost đổi phase law; constants uniform, thứ tự q,T,epsilon,delta rõ. Local curvature hội tụ −1/2, không gán decay q^(−alpha) cho nó.
- [ ] A13 — Evidence đúng regime: near actual mu_U, epsilon~q^(−3/2), budget scale N~q và q-growing; plot normalized regret, exploration fraction, phase errors và stopping tails. Integer evidence tại mu0=.75 không kiểm allocation boundary. Compare known-A oracle, recover-first, blind, partial-A và full algorithm cùng budget conventions.

Không bắt buộc cho static submission: toàn A01–A13. Bắt buộc nếu abstract/title claim adaptive Gamma hoặc matching total regret.

## Query: theorem về mất thông tin phải dẫn đến sửa representation có ý nghĩa

Same-summary/different-target và gap/2 floor là nguyên lý identifiability cơ bản; triangle inequality/XOR alone chưa là headline mới. State abstraction với value bounds cũng đã có. [Ferns–Panangaden–Precup](https://arxiv.org/abs/1207.4114).

- [ ] Q01 — Chốt query target, horizon, continuation policy và available representation. Phân biệt interventional target với observational surrogate, prediction error với decision regret.
- [ ] Q02 — Nêu một contribution vượt E5 triangle bound: hierarchy của sufficient representations, minimal-cost augmentation, hoặc sharp limitation/repair theorem trong physical model cụ thể.
- [ ] Q03 — Construct physically valid paired worlds/states có cùng representation nhưng target khác; kiểm transitions, action legality và observation receipts, không chỉ arbitrary tables.
- [ ] Q04 — Natural reachable evaluation panel có nonconstant targets. Audit vì sao 336 degenerate: filters, target definition, reward/horizon, reset distribution. Preconstructed delivery states là positive control, chưa là replacement population.
- [ ] Q05 — Report mọi generated/filter/degenerate/evaluable count, fixed inclusion rules trước kết quả; không lọc chỉ giữ các trạng thái method đẹp.
- [ ] Q06 — Exact optimal decoder trên small cases để tách information insufficiency với decoder incompetence. Baselines full-state oracle, restricted-information oracle và minimal augmentation.
- [ ] Q07 — Budget sweep acquisition/representation repair nối đúng theorem; nếu semantics/frontend không là novelty, giữ ngoài claim. Synthetic .5052 insufficiency và floor .4218 vẫn là evidence lý thuyết, không bị vứt bỏ vì runtime thiếu.
- [ ] Q08 — Nếu claim transfer/generalization: giữ mapping semantics/reference/support/continuation, derive bounds hoặc đo heldout distribution thật; không suy transfer từ correlation hay synthetic identifiability.
- [ ] Q09 — Reproducible executable environment and inference cost; evaluate uncertainty/failures. Nếu natural task luôn constant và không có theorem mới đủ mạnh, thu hẹp claim hoặc gộp vào Support.

## MASTER: từ contract đúng đến mua evidence đáng giá

Một concrete physical-query contract đã có sound proof. Không còn đúng khi nói toàn bộ sound đều là assumed fields. Nhưng composition triangle inequality và finite minimum-cost completion existence chưa tạo một algorithmic cost law. Task-relevant data sufficiency và decision value of information là prior mạnh. [Bennouna et al.](https://arxiv.org/abs/2602.15365), [Blackwell](https://doi.org/10.1214/aoms/1177729032).

- [ ] M01 — Chọn một concrete CIG family và target regret/cost; instantiate toàn chain model→support→reference→score→query→decision. Tránh abstract sound fields gánh mất headline.
- [ ] M02 — Với reference/transfer composition, derive hoặc đo đúng assumptions hTarget/hDownstream và error terms từ actual observations. Không tự gọi triangle upper là theorem về downstream regret khi bridge được nhập sẵn.
- [ ] M03 — Prove floor khi chỉ có evidence A, và matching cost để mua evidence B phá floor, trên **cùng** family, units và oracle. Generic information-ordering definition không đủ.
- [ ] M04 — Cho constructive acquisition/completion policy; nêu optimization oracle cost/complexity. “Finite set có minimum” không là efficient completion algorithm.
- [ ] M05 — Tính mọi chi phí, gồm acquiring certificate, preprocessing và exact fallback; không loại những instance mà certifier chậm hơn exact solver.
- [ ] M06 — Nếu bán reuse/amortization, prove/measure break-even theo số decisions/budgets/drift; cache invalidation/refresh assumptions cụ thể. Small instances hiện certifier chậm hơn exact là hạn chế phải giữ.
- [ ] M07 — Heldout replay Gamma_box và actual operational regret/cost, baseline always-exact, always-Top-C, naive certificate, no reuse, relevant oracle; kết nối đúng benchmark definition.
- [ ] M08 — Chứng minh novelty độc lập sau khi bỏ những theorem do D6/Support/Functional sở hữu. Nếu còn lại chỉ framework tổng hợp, phù hợp capstone/system paper chỉ khi evaluation/architecture contribution đủ; nếu không, gộp.

## Thứ tự thực hiện để tránh tiếp tục tản lực

1. **Chốt hai gói có lõi mạnh:** Structural S01–S05 và D6 D01–D07. Đừng để Pinsker hay full Gamma chặn static theorem package.
2. **Functional:** giữ kết quả v4 đã kiểm; đóng baseline F02 và full-alternative F04–F07. Không chạy tiếp shift50 với narrative drift.
3. **Support:** U03–U05 là nghiên cứu thật. Witness/contract đã có, không viết lại.
4. **Query:** Q03–Q06 là phép quyết định có runtime contribution hay chỉ theory subresult. Cần sửa đúng target/evaluation mechanism trước thêm seeds.
5. **MASTER:** M03–M06 quyết định có paper riêng hay nên gộp. Các pipeline checks là hỗ trợ, không thay quantitative novelty.
6. **D6 adaptive:** tiếp tục A01–A13 như chương trình mạnh hơn; kết quả epoch hiện tại là thành phần, không gắn nhãn completion cả chuỗi.

## Toàn bộ literature dùng trong đánh giá này

Các mục dưới là toàn bộ paper được viện dẫn trong bản đánh giá này, không tuyên bố liệt kê mọi citation từng có trong hàng trăm addendum. Link ưu tiên bản tác giả, proceedings hoặc publisher. Preprint 2026 được ghi rõ, không tự xem là kết quả đã peer-reviewed. Nhận định novelty là so sánh phạm vi, không phải bảo đảm chưa tồn tại equivalent theorem.

1. **Omar Bennouna, Amine Bennouna, Saurabh Amin, Asuman Ozdaglar (2026). _Data Informativeness in Linear Optimization under Uncertainty_.** arXiv:2602.15365. [Full PDF](https://arxiv.org/pdf/2602.15365). Support/MASTER; đọc Corollary 1 và Proposition 10, cùng non-adaptive setup.
2. **Marc Jourdan, Rémy Degenne, Emilie Kaufmann (2023). _Dealing with Unknown Variances in Best-Arm Identification_.** ALT 2023; arXiv:2210.00974. [Paper](https://arxiv.org/abs/2210.00974). Functional; variance, allocation và stopping.
3. **Ruitong Huang, Mohammad M. Ajallooeian, Csaba Szepesvári, Martin Müller (2017). _Structured Best Arm Identification with Fixed Confidence_.** ALT, PMLR 76:593–616. [Proceedings](https://proceedings.mlr.press/v76/huang17a.html). Functional; broad micro-observation formulation, specific LUCB-micro assumptions.
4. **Weiran Huang, Jungseul Ok, Liang Li, Wei Chen (2018). _Combinatorial Pure Exploration with Continuous and Separable Reward Functions and Its Applications_.** IJCAI 2018. [Author PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2018/05/ijcai18_CPE-CS.pdf). Functional; separable rewards/oracle framework, không tự đồng nhất raw-cell range model.
5. **Yuriy Dorn, Aleksandr Katrutsa, Ilgam Latypov, Anastasiia Soboleva (2025 preprint; AAMAS 2026). _Functional multi-armed bandit and the best function identification problems_.** [Paper](https://arxiv.org/abs/2503.00509); [author publication page](https://ooaarg.github.io/publications/functional-bandit/). Best function minimum khác response range, nhưng functional-arm viewpoint đã có.
6. **Qiaoqiao Wang, Wei You (2026). _Ranking-and-Selection with Multiple Correct Answers and Non-Answerable Estimates_.** arXiv:2606.21889. [Paper](https://arxiv.org/abs/2606.21889). Answer-wise acceptance/GLR, characteristic value và ENDS recipe; không mặc định mọi optimality guarantee đã prove.
7. **Aurélien Garivier, Emilie Kaufmann (2016). _Optimal Best Arm Identification with Fixed Confidence_.** COLT, PMLR 49:998–1027. [Proceedings](https://proceedings.mlr.press/v49/garivier16a.html). D6/Functional; characteristic time và Track-and-Stop.
8. **Rémy Degenne, Wouter M. Koolen, Pierre Ménard (2019). _Non-Asymptotic Pure Exploration by Solving Games_.** NeurIPS 32. [Proceedings](https://proceedings.neurips.cc/paper/2019/hash/8d1de7457fa769ece8d93a13a59c8552-Abstract.html). Structured exploration game và allocation via online learners.
9. **Rémy Degenne (2023). _On the Existence of a Complexity in Fixed Budget Bandit Identification_.** COLT, PMLR 195. [Proceedings](https://proceedings.mlr.press/v195/degenne23a.html). Fixed-budget complexity limitation; không tự suy fixed-confidence result.
10. **Steven R. Howard, Aaditya Ramdas, Jon McAuliffe, Jasjeet Sekhon (2021). _Time-uniform, nonparametric, nonasymptotic confidence sequences_.** Annals of Statistics 49(2):1055–1080. [Paper](https://arxiv.org/abs/1810.08240). Time-uniform coverage; confidence sequence không là novelty riêng của D6.
11. **Jannis Kurtz (2026). _Bounding the optimal number of policies for robust K-Adaptability_.** Mathematical Programming. [Publisher](https://link.springer.com/article/10.1007/s10107-026-02329-1); [author PDF](https://optimization-online.org/wp-content/uploads/2024/09/main-3.pdf). Structural; uncertainty dimension, convexity, continuity, concavity.
12. **Aaron Bernstein, Yann Disser, Martin Groß, Sandra Himburg (2022; online 2020). _General bounds for incremental maximization_.** Mathematical Programming 191:953–979. [Publisher](https://link.springer.com/article/10.1007/s10107-020-01576-0). Structural; all-prefix incremental setting. Không trộn author list này với phiên bản hội nghị trước đó.
13. **Marcin Bienkowski, Joakim Blikstad, Jarosław Byrka, Martín Costa, Yann Disser, Annette Lutz (2026). _Incremental Submodular Maximization: Better Than Greedy_.** arXiv:2606.28558. [Paper](https://arxiv.org/abs/2606.28558). One-ordering monotone submodular setting; khác menu/cancellation/additive-error claim.
14. **Shervin Javdani, Yuxin Chen, Amin Karbasi, Andreas Krause, J. Andrew Bagnell, Siddhartha Srinivasa (2014). _Near Optimal Bayesian Active Learning for Decision Making_.** AISTATS; extended arXiv:1402.5886. [Paper](https://arxiv.org/abs/1402.5886). Support; decision-region determination và HEC.
15. **Olivier Bousquet, Steve Hanneke, Shay Moran, Nikita Zhivotovskiy (2020). _Proper Learning, Helly Number, and an Optimal SVM Bound_.** COLT. [Paper](https://arxiv.org/abs/2005.11818). Helly/learning connection; không tự cho physical membership law.
16. **Norman Ferns, Prakash Panangaden, Doina Precup (2004). _Metrics for Finite Markov Decision Processes_.** UAI 2004, pp.162–169; arXiv upload 2012. [Paper](https://arxiv.org/abs/1207.4114). Query; state abstraction/bisimulation và value bounds.
17. **David Blackwell (1953). _Equivalent Comparisons of Experiments_.** Annals of Mathematical Statistics 24(2):265–272. [DOI](https://doi.org/10.1214/aoms/1177729032). Foundational decision-theoretic citation; publisher body không truy cập được trong lượt kiểm này, không dùng làm căn cứ khẳng định một specific new theorem bị subsume.
18. **Emanuele Borgonovo, Max D. Morris, Elmar Plischke (2018). _Functional ANOVA with Multiple Distributions: Implications for the Sensitivity Analysis of Computer Experiments_.** SIAM/ASA Journal on Uncertainty Quantification. [Paper](https://arxiv.org/abs/1801.05186). Reference dependence và multiple-distribution decomposition.
19. **Benjamin Lengerich, Sarah Tan, Chun-Hao Chang, Giles Hooker, Rich Caruana (2020). _Purifying Interaction Effects with the Functional ANOVA: An Efficient Algorithm for Recovering Identifiable Additive Models_.** AISTATS, PMLR 108:2402–2412. [Proceedings](https://proceedings.mlr.press/v108/lengerich20a.html). Main/interaction-effect purification; không phải exact D6 minimax law.

20. **Kellen Kanarios, Qining Zhang, Lei Ying (2024). _Cost Aware Best Arm Identification_.** arXiv:2402.16710. [Paper](https://arxiv.org/abs/2402.16710). Expected acquisition cost, lower bound và asymptotically matching CTAS; so sánh cho D6/MASTER priced-query hướng mới.

## Evidence và cách kiểm lại

- Script: `scripts/audit_publication_snapshot_20260911.py`.
- Snapshot có hashes, từng module, audit declarations, raw-row recomputation và paired CIs: `research/high_risk_20260910/publication_snapshot_20260911.json`.
- Previous exact/MC audit: `research/high_risk_20260910/completed_experiment_evidence_v1.json`.
- Reference exact reduced-game certificates: `research/high_risk_20260910/d6_reference_phase_certificates_v1.json`.
- Mathematical derivation: `work/p13_conjectures/D6_REFERENCE_PHASE_DERIVATION_20260911.md`.
- Current selected closure manifest: `research/high_risk_20260910/chain_closure_manifest.json`; closed/open prose là đánh giá có scope, không self-proving theorem.

Lệnh read-only đối với input (chỉ ghi snapshot riêng):

```bash
cd /Users/phanan/cig-amf-main
.venv/bin/python scripts/audit_publication_snapshot_20260911.py
```
