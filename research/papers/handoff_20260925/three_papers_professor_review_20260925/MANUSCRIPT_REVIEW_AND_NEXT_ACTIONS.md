# Bản thảo A/B/C sau review nội dung — 25/09/2026

Đã sửa trực tiếp sáu file `.tex` trong `research/papers/_tex`, gồm ba bài và ba supplement. Bản trước sửa lưu nguyên byte tại `research/papers/legacy/manuscripts_before_review_20260925/`, có SHA256. Không sửa ledger/ROADMAP/CLAIMS, không sửa Lean, không compile, không chạy solver hoặc lấy mẫu lại. Các PDF manuscript cũ chưa phản ánh bản LaTeX mới.

## 1. Đã thay đổi gì và tại sao

### Paper A: từ sai geometry đến chi phí sửa và chi phí learner

Chuỗi bài hiện tại:

1. Định nghĩa loss của compression thật và strict alternatives; nối Gaussian KL trên cùng parameter class.
2. So hai optimum; chứng minh tất cả exact/near-optimal frozen designs bỏ đói middle directions.
3. Repair frontier có hai cận cụ thể, không tuyên bố một công thức exact chưa chứng minh.
4. Bổ sung certificate tổng quát: frozen upper certificate `c`, true-alternative loads `ell_j`, trọng số `nu_j`, và điều kiện cover từng cell.
5. Từ `Lambda J_true(w) <= sac(w)` đến `N sac(N/N_total) >= Lambda D`.
6. Dựng lại đầy đủ learner lý tưởng trong bài, rồi so tốc độ của nó với surrogate learner cụ thể.
7. Đọc đúng finite-budget evidence, gồm cả swapped-world reversal và nhược điểm answer selection của implementation.

Các sửa toán/phạm vi:

- **Statistic stopping:** trước đây gọi là exact GLR nhưng không chỉ rõ ridge. Đã viết
  `Z_t^a(T) = inf_{lambda in Alt_T} (1/2) sum_e N_e(t)^2 (mu_hat_e-lambda_e)^2 / ((a+N_e(t)) nu_e)`
  và threshold `log(1/delta)+(1/2)sum log(1+N_e/a)`. Đây là đúng `qAbs/glr` của `LeanPaperA7GLRMeasV1`, không phải log-GLR Gaussian thường. Đã thêm quota post-warm, forced mixture, grid, tie rule, hitting time có thể vô hạn, và martingale dùng để chứng minh correctness.
- **Generic repair converse:** công thức đúng là
  `R(b) >= min(1,b/sac(v)) J_true(v)` với `sac(v)>0`, không phải công thức không clip ở mọi `b`. Proof bằng mixture đã viết đầy đủ. Theorem Lean `repair_mix` đúng; chỉ prose đầu module `LeanPaperASacrificeDualityV1` còn bỏ điều kiện khi diễn giải sang biến budget.
- **Thang rM:** các cận exact giữ mọi `r>=1,M>0`; các Theta có universal constants theo `rM` nay ghi `rM>=1`. Không ngoại suy ngược về `rM -> 0`.
- **Attainment:** construction bảo đảm đạt ít nhất lower bound; không gọi nó là equality của true frontier.
- **Padding:** bốn frozen cells là hai A và hai B anchors, không phải bốn A cells.
- **Forcing:** lower bound Omega(log) khi a=1 không phải chứng minh upper bound; đã bỏ cách nói “only” gây hiểu lầm.
- **Finite alpha:** theorem không cung cấp delta_0 số để nói 0.05 “lớn hơn nhiều delta_0”. Đã bỏ suy đoán đó. Không dùng panel để chứng minh log-squared law.
- **Numerical optimiser:** geometry là ascent trên lower certificate, không phải global true-game oracle. Caption giải thích cả nhãn cũ còn trong hình.
- **Prior art:** giữ Bennouna/Jourdan và các bài sát nhất. Mô tả Bennouna nay có prior knowledge/uncertainty set, không giản lược thành một yêu cầu full-rank vô điều kiện.

Module mới được đưa vào mạch bài: `LeanPaperASacrificeDualityV1`; các mắt nối learner được diễn giải từ `A7IdealLearner`, `A7GLRMeas`, `A7IdealStop`, `A7IdealFamily`. Không có theorem mới được giả làm đã compile.

### Paper B: obstruction/order, rồi chi phí phân bổ query

Chuỗi bài hiện tại:

1. Common safe answer và obstruction; chỉ xét cặp world khác nhau.
2. Obstruction information lower bound cho protocol thật; extension cho almost-sure stopping bằng truncation.
3. Bổ sung stronger lower law với **giả thiết mạnh hơn được ghi rõ**: per-query second moment `int p_w^2/p_u <= exp(t)`.
4. Tournament upper bound; bổ sung dùng chung block mẫu theo query.
5. Private-query Gaussian construction chỉ ra scalar obstruction không chứa chi phí phân bổ giữa nhiều query.
6. Graded order law; hai channel cụ thể với matching exponents và actual compression losses.

Các sửa/phần bổ sung:

- **Lượng từ menu:** cận dưới uniform trên mọi finite admissible linear menu; cận trên chỉ cho menu chứa decision probe/tail probe cần thiết. Menu toàn zero probes không có upper rate hữu hạn ấy. Abstract và theorem đã thống nhất với limitation này.
- **Overlapping answers:** `s_safe = min sep` chỉ cho correspondence `safe(w)=W\{w}`; không cho mọi overlapping correspondence. Pairwise intersection cần `|W|>=3`.
- **Channel:** formal protocol là positive measurable densities trên R, finite worlds/queries và dummy chung. Không quảng bá thành mọi singular observation kernel hay continuum query policy.
- **Shared tests:** `|Q| ceil(log(|W|/delta)/t_H*)`, hoặc chọn nhỏ hơn với schedule `|W|^2`. Proof giải thích vì sao dependence giữa tests dùng chung mẫu không ảnh hưởng union bound; tie orientation vẫn antisymmetric.
- **Private queries:** tại world 0, mỗi alternative j buộc chi phí riêng ở query j; tổng lower bound có factor k. Không tuyên bố quadratic world factor là cần thiết.
- **Chi-square lower:**
  `P_w(N t <= y) <= delta + 2(|H|-1)sqrt(delta exp(y))`,
  rồi expected bound với cardinality chỉ ở trong log. Không nhận rằng finite KL tự suy ra second-moment condition; statement mới này giữ finite horizon đúng với module.
- **Cost:** paid non-dummy không đồng nghĩa mọi query đều informative cho mọi pair. Một shared schedule có dummy block thì paid cost <= horizon; không tự đồng nhất cả hai.

Các module đưa thêm vào manuscript/supplement: `LeanPaperBChiStarV1`, `LeanPaperBPrivateQueryV1`, `LeanPaperBShareTournamentV1`.

### Paper C: frontier, timing, rồi bảo đảm robustness đúng lượng từ

Giữ các kết quả mạnh đang có: full even frontier, **full odd frontier** (không còn chỉ zero-band/breakpoint), same-law attainment, physical regret identification, flow equivalence, banded ex-post frontier.

Lỗi quan trọng đã sửa: theorem lower bound là cho mọi perturbation, nhưng upper bound chỉ do **một** perturbation đạt được. Không suy ra “mọi perturbation vượt 1/m đều làm price collapse”.

Phản ví dụ viết ngay trong paper:

`g'=(1+epsilon/(m+4)) g_m` có l1 distance epsilon nhưng prefix, baseline, normalizer cùng scale. Mọi normalized value và price ratio giữ nguyên, kể cả khi epsilon cố định còn m tăng.

Thay vì hạ mất câu chuyện, đã chứng minh một kết luận mạnh và đúng:

`R_m(epsilon) = inf_{||g'-g_m||_1<=epsilon, V(g';m)>0} V(g';0)/V(g';m)`.

Với m lẻ >=3, 0<epsilon<=1/6:

`(1/16) min(m-1,1/epsilon) <= R_m(epsilon) <= min((m+3)(m-1)/(2m),10/epsilon) <= 10 min(m-1,1/epsilon)`.

Đây là luật đúng bậc cho mức giá **còn bảo đảm được trên cả ball**. Có proof hoàn chỉnh trong main paper: universal lower chuyển qua infimum; upper dùng g_m và one-item witness. Không cần giả định tồn tại minimizer.

Các chỉnh khác:

- Ratio không “vanish”; premium trên 1 mới biến mất.
- Hình robustness floating point không tự là phản chứng theorem; một vi phạm sẽ phải audit model/solver/normalization.
- Search tìm ratio thấp trả upper bound cho infimum trên miền search, không chứng nhận global worst-case lower bound.
- Abstract không còn nói perturbation curve exact; exact frontier và robustness up to constants được phân biệt.

Corollary infimum-over-balls là **proof toán mới trong manuscript**, dựng từ Lean inputs hiện có. Chưa có Lean wrapper riêng và được ghi rõ cả main/supplement. Không đổi định nghĩa loss để cứu một claim sai.

## 2. Đối chiếu progress thật: không giao lại các nợ đã đóng

Snapshot byte/hash của gate tại thời điểm audit:

- `full7_20260925`: 219 modules (204 roots, 15 dependencies), 1704 audit prints, PASS; 0 source drift.
- `smokeR2_20260925`: 96 modules, 771 prints, PASS; 0 source drift.
- `smokeSHARP1_20260925`: 35 modules, 337 prints, PASS; 0 source drift.
- Union phủ **209/210** `LeanPaper*.lean`; file chưa thuộc ba completed matching gates là `LeanPaperBShareTournamentV1.lean`.
- Không cộng ba số audit prints vì có import trùng.

**A ideal OperationalFinish không còn là nợ cũ.** Đã đọc các theorem family/ideal/direct/upper/stopped liên quan: learner lý tưởng đã có endpoint. Điều chưa được suy ra là finite-precision implementation bằng learner lý tưởng.

**B không còn chỉ là finite alphabet hay deterministic policy.** Protocol continuous density và randomized adaptive policy đã có; lower cho unbounded stopping cũng có riêng. Mỗi theorem vẫn phải giữ hypotheses của channel/menu/second moment như đã ghi.

**C không còn chỉ numerical per-size hoặc odd breakpoint.** All-m frontiers và actual physical objective đã có. Đừng quay lại viết lại window classification hay C2.

Coverage này là bằng chứng build + nguồn khớp. Nó không có nghĩa tôi đã line-by-line kiểm lại mọi proof body của 210 modules. Đã đọc nội dung cả ba manuscript, các phần supplement có liên quan, cùng các định nghĩa/chuỗi theorem và producer/artifact dùng cho các kết luận trên. Supplement B giữ nhiều phần lịch sử; phần ngoài các chuỗi đang dùng được tra có mục tiêu, không tuyên bố đã tái thẩm định toàn bộ mọi proof lịch sử.

## 3. Results đã kiểm trên dữ liệu cũ — không lấy mẫu/solve lại

Chi tiết máy đọc được: `SAVED_EVIDENCE_VERIFICATION.json`; script: `verify_saved_evidence.py`.

- **A fixed-design certificates:** dựng lại 972/972 KKT certificates bằng Fraction từ region/multipliers, kiểm all-region coverage, primal feasibility, nonnegative dual, stationarity, complementary slackness và objective. Đây là hai fixed-design families, không tự biến thành proof của outer optimized Gamma.
- **A paired panel:** 7200 launched, 6258 stopped, 942 censored, 0 stopped-wrong. Counts cộng đúng tau, summaries đúng raw records; producer và imported rules hashes khớp.
- **A7 panel:** 600 runs, 1 censored, 0 stopped-wrong. Swapped world vẫn là một phát hiện thuật toán quan trọng: learner 3801 so oracle diagnostic 1109 và uniform 1679; selection luôn A, kept set luôn {A,B}. Không che nó bằng mean gộp.
- **B formal decoder:** tính lại 616 simultaneous two-sided CP intervals từ error counts; maximum discrepancy ~1e-15; 11 certified upper budgets và 5 chưa certify. Dùng đúng `paperB_decoder_leanfallback.json`, không nhầm artifact đời trước. Certified budgets là upper bounds cho decoder cost; không phải minimax sample-complexity estimates.
- **C formula panel:** 77 stored rows, m=3..9; ex-ante/ex-post formulas khớp LP floats tới khoảng 1e-16. Không gọi floating equality là exact certificate.
- **C perturbation:** 220 rows, không thiếu grid entry, không vi phạm envelope 3*l1/min(D,D'); largest ratio .3224. Không resolve LP nên không chứng nhận lại optimality của từng float.
- **C provenance:** stored producer hash của perturbation khác source hiện tại. Source sau thêm logging; không sửa JSON lịch sử để làm nó giả khớp.

Một lỗi producer còn nên sửa trước chạy mới, không cần chạy lại dữ liệu cũ: `scripts/EXP_paperA7_panel.py` khoảng 186–190 và `scripts/EXP_paperA_deployable.py` khoảng 359–364 còn test wrong/stopped đối chiếu alpha. Delta-correctness là wrong/launched. Phân tích trong manuscript nay dùng all-launched và zero-errors không được gọi coverage proof. Nếu sửa producer, lưu version/source hash cũ; imported source hash của paired run phải giữ đúng snapshot lịch sử.

## 4. Legacy đã giúp khôi phục đúng lịch sử

- CFamily hiện tại byte-identical bản ORIGINAL tìm được; không tiếp tục tuyên bố API gốc của nó “mất vĩnh viễn”.
- BSafeOrder ORIGINAL đã có lỗi diagonal trong Together. Bản hiện tại thêm distinctness/singleton regression; đây là sửa mô hình thật, không chỉ sửa cú pháp.
- Các helper construction trong bản MY_NEW của CFamily vẫn nằm ở các module hiện tại khác; không cần nhập trùng lại.
- API ENat của MY_NEW_BSafeOrder là nhánh archive, không đồng nghĩa API ORIGINAL bị mất.
- Prototype `FunctionalRangeContrast` chưa accepted không phải theorem đã đóng. Lập luận so resistance không tự cho so energy khi gap khác nhau; không đưa nó thành headline bổ sung.

## 5. Việc worker cần làm để bàn giao bản PDF đúng nội dung này

### Bắt buộc trước khi gọi bản này là bản release

1. Compile **sáu** `.tex` hiện tại, không dùng PDF cũ. Kiểm undefined references/citations, overfull boxes, theorem/equation wrapping và vị trí figures. Không đổi toán để giải layout. Static check đã pass nhưng không thay LaTeX compile/render.
2. Cho `LeanPaperBShareTournamentV1` và import closure qua frozen gate. Đọc axioms và source hash của đúng snapshot. Nếu fail, sửa proof tương ứng; không đổi theorem thành nhận error bound/decoder law làm input. Sau PASS mới bỏ draft release note trong main và supplement B.
3. Rà các hình cũ theo caption mới, ưu tiên `paperA_deployable.pdf`: legend `true game at estimate` phải đổi thành `geometry lower-certificate heuristic`. Dùng JSON đã có; không chạy experiment lại. Hình C panel phải đọc là universal lower/existential construction upper, không phải curve của mọi perturbation. Caption hiện tại đã làm rõ ngay cả trước khi sửa artwork.
4. Giữ phân biệt lý tưởng/implemented learner. Không đổi finite-budget plot thành evidence cho asymptotic optimality; không giấu swapped-world failure. Thay implementation là một experiment/version mới nếu sau này muốn chứng minh một claim algorithmic mạnh hơn.
5. Giáo đọc các theorem/scope và novelty comparison ở ba bài; một bản compile sạch không dự đoán quyết định nhận bài của venue.

### Để tất cả corollary mới cũng có Lean wrapper riêng (không cần tìm toán mới)

**C robust ball:** tạo module mới nhập CEndgame, CCollapseScale, CCollapseWindow và bridge trueValue_family.
- Định nghĩa set ratio của g' trong ball và positive free value.
- Witness nonempty g_m; positivity từ free closed form.
- Lower uniform: tách d=0 và d>0; dùng collapse_all ở d, monotonicity `1/epsilon <= 1/d`.
- BddBelow theo lower vừa chứng minh; dùng csInf_le cho g_m và gD(epsilon).
- Kết luận hai phía như trong paper. Không nhận lower/upper ratio làm hypotheses cuối.
- Có thể thêm scale invariance của b_k và normalized regret để formalize counterexample; không cần enumerate m.

**A clipped repair:** wrapper của `repair_mix`, đặt lambda=min(1,b/sac(v)); chứng minh 0<=lambda<=1 và lambda*sac(v)<=b. Không kéo dài affine mixture ra ngoài simplex. Sửa prose đầu `LeanPaperASacrificeDualityV1` cho đúng; theorem hiện tại không sai.

Không gọi hai wrapper là đã Lean-checked trước khi compile. Bản thảo hiện đã có proof toán đầy đủ và không gán sai trạng thái cho chúng.

### Không phải việc bắt buộc để giữ story hiện tại

- Không cần thêm seed hàng loạt, solve lại 972 regions, viết lại C2/C3, hay làm lại A7 ideal chain.
- Một practical implementation đạt theorem ideal, một channel query continuum, hay exact arbitrary-weight C frontier đều là kết quả mạnh hơn khác; bài hiện tại không claim chúng.
- General repair certificate là weak duality; chưa có theorem strong duality cho mọi class. Giữ câu đó như hiện tại, không thêm “exact characterization” tùy tiện.

## 6. Kiểm tra bản thảo và nguồn tham khảo

`TEX_STATIC_CHECK.json`: cả sáu file không có lỗi tĩnh tìm thấy: balanced braces/environments, labels không trùng, references/citations resolve nội bộ, figures tồn tại, Lean module names tồn tại, không control characters. Kiểm tra này không kiểm chứng proof bằng kernel và không đo layout.

Đã kiểm lại metadata/abstract trên nguồn primary của các bài sát A/B: [Huang](https://arxiv.org/abs/2608.02267), [Wang–You](https://arxiv.org/abs/2606.21889), [Bennouna 2026](https://arxiv.org/abs/2602.15365), [Bennouna 2025](https://arxiv.org/abs/2505.21692), [Wan et al.](https://arxiv.org/abs/2602.05340), [Schutte et al.](https://arxiv.org/abs/2505.03953). Không dùng việc có bibitem như bằng chứng rằng novelty đã được chứng nhận. Lượt này không phải một lần đọc lại 500/1000 full papers; crosswalk 82 nguồn sát đã được đưa về repo để tham khảo.

Các contribution nên bảo vệ: A là quantitative starvation/repair/policy consequence trên cùng model; B là obstruction cộng observation order và chi phí query, với explicit matching examples; C là exact frontiers/timing cùng robustness guarantee. Confidence sequences, weak duality, union bounds, martingale và LP flow là công cụ, không nhận là phát minh của ba bài.
