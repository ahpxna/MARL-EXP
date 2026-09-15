# Việc nên làm tiếp theo cho sáu paper CIG-AMF

Ngày đánh giá: 7/9/2026. Mục tiêu giả định: đưa các kết quả hiện có thành những submission có đóng góp riêng và bằng chứng đủ mạnh, với chi phí nghiên cứu hợp lý.

**Quyết định đề xuất:** ưu tiên chốt Functional và Structural; phát triển MASTER trên lõi chứng nhận đã có; giữ Query ở giai đoạn hoàn thiện thực nghiệm; tích hợp Support vào MASTER trừ khi vượt qua cổng lý thuyết riêng; dành cho D6 một đợt đóng kết quả hữu hạn, có điều kiện dừng rõ ràng.

Đây là kế hoạch từ việc đọc report, đối chiếu nguồn bổ sung và kiểm tra một số suy luận. Không phải xác nhận rằng toàn bộ Lean corpus đã được biên dịch lại hoặc mọi thí nghiệm đã được tái lập.

## 1. Trước hết: đồng bộ trạng thái bằng chứng

Gói PDF ngày 5/9 có 122 trang. Sáu individual report lần lượt có 21, 18, 18, 19, 27 và 19 trang. Tuy nhiên, `source_addenda/` có thêm hai bản D6 mà PDF và supplementary ngày 5/9 chưa phản ánh đầy đủ:

| Nguồn | Trạng thái được nguồn ghi nhận | Có thể xác nhận từ gói này |
|---|---|---|
| D6 addendum A, 5/9, §§72–91 | Centered RankOne bị bác bỏ bằng số học exact; V2 chưa có artifact biên dịch. D6-prime còn mở. | Có witness JSON, V2 source và các module thành phần; không có V2 `.olean` trong snapshot. |
| D6 addendum B, 5/9, §§92–101 | V2 đã compile và audit 16 theorem. | Nguồn ghi nhận kết quả; artifact V2 mới và file audit được viện dẫn chưa nằm trong supplementary này. |
| D6 addendum C, 6/9, §§102–110 | D6-prime bị bác bỏ; có binary integer witness với 2D=86, δ=17, 86>85. Module binary chưa compile. | Có mô tả trong `.tex`; chưa có bảng 64 giá trị, verifier và module binary được viện dẫn để tái kiểm tra trong gói này. |

**Việc làm đầu tiên:** tạo bản bổ sung có version mới, kèm nguồn, witness, scripts, Lean toolchain/dependency lock, compile log, axiom audit và manifest/hash. Giữ bản lịch sử append-only; manuscript mới chỉ trình bày trạng thái hiện hành. Sự có mặt của `.olean` tự nó không thay thế một clean build có thể tái lập.

Trong mọi manuscript, tách rõ: theorem đã chứng minh; exact computation; development experiment; confirmatory experiment; conjecture. Mỗi kết quả chỉ cần một paper sở hữu chính; các paper khác viện dẫn và trình bày phần cần thiết.

## 2. MASTER — chốt lõi deterministic, triển khai utility, giới hạn mở rộng

**Câu chuyện chính:** các nghĩa vụ bằng chứng response/reference/support/interaction/query có thể không thay thế được nhau; điều kiện cấu trúc có thể loại bỏ một số nghĩa vụ; hệ thống chỉ ra quyết định khi những nghĩa vụ còn lại đã được đáp ứng.

**Cơ sở hiện có:** năm kiểu obstruction và direct-product indispensability; structural elimination; regret certificate; Γ_box ≤ Γ_op; paired development replay 1.800 instance × 9 tolerance. Ở ε=0,01, fallback giảm từ 93,61% xuống 45,67%. Cả hai nhánh có zero observed false-safe trong artifact được thiết kế với interval chứa truth.

**Ba việc tiếp theo:**

1. Viết bản manuscript hiện hành với theorem chính, giả thiết, các obstruction/elimination và ví dụ đầu-cuối; tránh biến nó thành bản tổng hợp sáu lịch sử nghiên cứu.
2. Đưa Γ_box qua regression của selector thực tế và chạy held-out paired replay. Báo cáo fallback theo tolerance, regret trên quyết định được chứng nhận, chi phí đo và latency. Resampling/CI theo base instance hoặc seed, không coi chín tolerance trên cùng instance là chín lần độc lập.
3. Nếu muốn tuyên bố learned/adaptive certification, xây một hợp đồng statistical validity riêng: mô hình quan sát, điều kiện noise/dependence, interval đồng thời và hiệu lực tại thời điểm dừng. Có thể dùng confidence sequences đã có; phải chứng minh giả thiết áp dụng vào quá trình CIG cụ thể.

**Cổng hoàn tất:** selector dùng đúng theorem/assumptions; utility có held-out evidence; manuscript hoặc giới hạn ở deterministic conditional guarantees, hoặc có statistical composition theorem phù hợp. Không bắt paper chờ sample-optimal acquisition.

**Giảm ưu tiên:** chạy thêm arbitrary random typed set cover để tìm hardness. Campaign sửa đúng có mean greedy/optimum 1,00226 và chỉ 87/3.000 gap; nếu nghiên cứu complexity, phải xuất phát từ obligation graph thật của CIG.

Nguồn: MASTER §§31–47; `MASTER_GAMMA_PAIR_DERIVED_SUMMARY_20260905.json`; `OBSERVATORY_CORRECTED_DERIVED_SUMMARY_20260905.json`.

## 3. Functional — paper gần chốt nhất về kết hợp theory và empirical

**Câu chuyện chính:** sai số response phải vượt qua hai rào cản khác nhau: extrema trong relation và thứ tự giữa các relation. Geometry quyết định khi nào có thể cấp certificate.

**Đã đủ để viết:** confirmatory root riêng có 20 seed, 60/60 cell; fixed panel ổn định; zero observed deterministic certificate violations. Top-k accuracy cuối khoảng 63,2%, Q-bound certificate coverage khoảng 12,08%, interval certificate khoảng 0,14%. Coverage thấp là giới hạn utility cần trình bày rõ; accuracy và certification là hai đại lượng khác nhau.

**Thí nghiệm bổ sung có giá trị nhất:** fixed-confidence, endpoint chính N_cert, so targeted acquisition với uniform và uncertainty-based allocation, dùng cùng confidence requirement, observation model và measurement cost. Chốt trước strata easy/mid/hard, budget cap và xử lý những run chưa đạt certificate. Không tính median chỉ trên run thành công: báo cả xác suất chứng nhận theo budget và censored runs.

Các oracle quantities như δ_Q° và true boundary gap dùng để phân tích cơ chế. Thuật toán deployable không được truy cập chúng để quyết định lúc dừng; nó phải dùng interval/envelope có thể tính từ dữ liệu.

**Selective maintenance:** để extension riêng nếu chưa có bằng chứng đủ mạnh. Muốn nâng thành đóng góp chính, phải freeze drift process độc lập, so selective/full/periodic refresh, tính nonzero post-refresh error, nhận diện tình huống full refresh vẫn không đủ và chuyển sang re-identification/fallback.

**Cổng hoàn tất:** manuscript core + kết quả confirmatory đúng phạm vi. Nếu headline là giảm chi phí certification, cần thêm confirmatory fixed-confidence study; nếu study chưa thành công, vẫn có thể chốt paper geometry với claim hẹp. Không ép selective maintenance vào critical path.

**Dừng:** hồi sinh universal fixed-budget superiority; chọn λ_D vì một summary đẹp; chạy thêm learning curves cùng thiết kế khi câu hỏi hiện tại là certificate utility.

Nguồn: Functional §§35–53; `CONFIRMATORY_RUN_COMPLETE.json`, `v7_analysis.json`, `v7_checkpoint_summary.csv`.

## 4. Support — sửa nghĩa “đủ để quyết định” trước khi tối ưu

**Lõi hiện có:** exact support radius, deficit/certificate hierarchy, one-bit witness, và theorem `Separates ↔ PartialTestCover`. Campaign exact hiện có giải được 315/315 instance, Q* từ 0 đến 7; đây không phải universal bound.

**Phát hiện mới trong lần đọc này:** tách mọi cặp có good sets rời nhau chưa đủ để bảo đảm một quyết định chung cho toàn bộ observation fibre. Theorem Lean được đóng gói chứng minh equivalence với predicate `Separates`; nó không tự chứng minh điều kiện giao toàn fibre của Query §51.

Một witness ngay trong support-radius model: ba relation, giữ một relation, f_j(a)=a_j. Ba support khả dĩ đều gồm anchor (0,0,0) và một điểm:

| World | Điểm còn lại | Radius khi giữ relation 1, 2, 3 | Zero-regret decisions |
|---|---|---|---|
| W1 | (1,1,-1) | (0,0,1) | {1,2} |
| W2 | (-1,1,1) | (1,0,0) | {2,3} |
| W3 | (1,-1,1) | (0,1,0) | {1,3} |

Radius được tính đúng bằng nửa oscillation của tổng relation bị bỏ. Với 0≤ε<1, mọi cặp good sets giao nhau, nhưng giao cả ba rỗng. Trên model class ba world này, Partial Test Cover có optimum 0. Tuy nhiên không-query không thể đưa ra quyết định tốt chung. Một query membership cho điểm (1,1,-1) đã đủ: trả lời có thì chọn relation 1; không thì chọn relation 3. Vì vậy decision-sufficient optimum là 1.

**Phạm vi:** đây không bác bỏ theorem `Separates ↔ PartialTestCover`. Nó bác bỏ bước suy rộng từ pair separation sang universal decision sufficiency nếu thiếu điều kiện bổ sung. Số liệu 315 instance hiện vẫn là số liệu cho objective đã tính, không được tự động đổi nhãn thành end-to-end decision query complexity.

**Thứ tự làm:**

1. Formalize witness trên và audit đường truyền `Separates → CertGate`. Kiểm tra từng leaf/fibre có giao good sets khác rỗng.
2. Chọn một phạm vi: chứng minh tính chất giao đôi kéo theo giao toàn bộ cho lớp support mục tiêu; hoặc mở rộng obstruction từ cặp world sang những nhóm world có giao good sets rỗng. Trong lớp hữu hạn, query set cần chia tách mỗi nhóm obstruction để không nhóm nào nằm nguyên trong một observation fibre.
3. Phân biệt nonadaptive query-set optimum với adaptive decision-tree cost. Reduction hiện tại không tự cho adaptive sample optimality.
4. Sau đó mới chọn một representation cụ thể như factor/CSP/shield, tìm structural law hoặc algorithm với assumptions và parameter rõ ràng; không theo cùng lúc năm loại width.

**Đóng gói:** mặc định là provider trong MASTER. Chỉ tách submission khi có kết quả riêng về decision-sufficient acquisition trên CIG support structure. Hypergraph reformulation tự nó cũng cần novelty audit.

Nguồn: Support §§47–55; `LeanSupportPartialTestCoverV1.lean`; Query §51. Witness trên là kiểm tra mới bằng số học hữu tỉ, chưa formalize Lean.

## 5. Structural — chốt exact theory; thêm companion algorithm có giới hạn

**Câu chuyện chính:** số ranking cần tái sử dụng để đạt optimum ở mọi budget. Lõi mới là χ_prefix(F_r,0)=r=|I_r|/2 trên staircase supportOsc family, không còn chỉ là lower/upper sandwich.

**Ba việc tiếp theo:**

1. Viết theorem-first manuscript và kiểm tra novelty của đúng object: menu các prefix chains chỉ cần chạm một acceptable set mỗi cardinality layer. So với incremental optimization, chain transversal và maximum-of-modular objectives. Generic chain-cover hoặc nhiều ranking không phải đóng góp mới tự động.
2. Đóng exact solver nhỏ làm oracle; triển khai Best-Chain + COVER-RANK. Phân biệt exact chain oracle, approximation oracle có guarantee và heuristic; không nhập approximation factor nếu không thỏa giả thiết oracle.
3. Báo curve ε_K hoặc χ_prefix(ε), worst-budget regret, runtime và memory. Baselines: Top-C, một ranking được tối ưu tốt, menu K ranking, và optimum riêng từng budget. Thử thêm family ngoài staircase để kiểm tra algorithm không chỉ ghi nhớ construction.

**Cổng hoàn tất:** theorem core có build tái lập, firstness audit đủ sâu và algorithmic story rõ. Không bắt paper theory chờ KPrefixNet/deep MARL. Nếu sau này làm neural extension, nó cần ablation riêng K=1/K>1 và changing budgets.

**Giảm ưu tiên:** tìm thêm small exact staircase case; mở lại approximate shell và các characterization đã bị bác bỏ. Cận universal m+1 cũng chứa hai endpoint budget 0,m được mọi ranking bao phủ miễn phí; bỏ chúng là cleanup dễ, không nên làm headline “sharp new upper bound”.

Nguồn: Structural §§38–59; `LeanStructuralStaircaseExactPrefixCoverV1.lean`.

## 6. D6 — sửa research target: upper bound đã có, sharpness mới là việc còn lại

**Đừng làm theo nguyên xi “next gate” của addendum C.** D6 §39 ngày 2/9 ghi theorem:

\[
D(S,T)\le |S\setminus T|\,\delta_\square
\]

cho Top-C S và equal-cardinality competitor T, dưới normalized nonnegative product reference và mixed-difference assumptions. Lấy T=T* tối ưu, |S|=|T*|=k:

\[
2D\le 2|S\setminus T^*|\delta_\square
\le2\min(k,m-k)\delta_\square\le m\delta_\square.
\]

Vì vậy upper bound m ở C §§107,110 là corollary của kết quả report đã ghi. Việc cần là lấy module `LeanD6SmallSymmetricDifference`, kiểm tra định nghĩa/giả thiết khớp và đóng wrapper; không phải mở một universal proof project mới. Module đó không nằm trong headline snapshot này nên chưa clean-build lại trong lần đọc này.

**Conjecture equality cần sửa miền:** với k=floor(m/2), m lẻ đã có upper bound m-1; do đó supremum=m không thể đúng cho mọi m như display §107 viết. Còn với m=2, k=1, binary corner reference, có thể chứng minh trực tiếp supremum=1, không phải 2.

Chứng minh m=2: sau gauge F(0,0)=0, viết F(1,0)=a, F(0,1)=b, F(1,1)=a+b+h. Khi đó δ=|h|. Đặt

\[
w(c,h)=\operatorname{range}\{0,c,c+h\}
=\max(|c|,|c+h|,|h|).
\]

Nếu |a|>|b|, Top-C giữ coordinate 1; doubled losses là w(b,h) và w(a,h). Vì w(b,h)≤|b|+|h| và w(a,h)≥|a|, ta có 2D≤|h|. Chọn a=-1-η, b=1, h=1 với 0<η<1: StrictTopC margin η, δ=1 và 2D=1-η. Lấy η→0+ cho supremum=1. Đây là suy luận đại số mới trong lần đọc này, chưa Lean formalization.

**Kế hoạch hữu hạn có giá trị nhất:**

1. Khôi phục artifact B/C và compile/audit binary integer witness 86>85. Tách phản ví dụ centered cũ và binary/raw mới trong provenance.
2. Đóng corollary upper bound 2min(k,m-k) từ symmetric-difference theorem; làm rõ m chẵn/lẻ, k, reference và strictness.
3. Trước khi generalize, biến near-extremal m=6 thành family symbolic F_η với η hữu tỉ: chứng minh StrictTopC, δ và hai loss trên một khoảng η>0, rồi chứng minh ratio tiến tới 6. Kết hợp upper bound sẽ đóng exact supremum m=6. Một dãy số LP gần 6 chưa tự là chứng minh sharpness.
4. Chỉ sau đó kiểm tra m chẵn≥4 bằng tangent-cone/cell LP hoặc constructive family. Một verified competitor đã đủ chứng nhận lower bound cho D; cần nhận diện đúng điều kiện tối ưu toàn cục khi muốn tuyên bố exact D.

**Cổng hoàn tất:** một theorem/refutation package khép kín, định nghĩa constant rõ và result tái lập được. Nếu general-m construction không tiến triển sau đợt nghiên cứu đã giới hạn, chốt m=6/theory note hoặc tích hợp vào MASTER; không kéo Functional/Structural chờ.

**Dừng:** cứu raw-rank-one m-1; dùng no-counterexample-found làm upper bound; tăng denominator để tìm geometry mới; ưu tiên reverse fibre inclusion chỉ để cứu decision bound đã bị bác bỏ.

**Hai câu cần hạ mức trong C:** một tie point thất bại khi rounding không chứng minh supremum không đạt ở mọi điểm khác; vài random tangent directions thất bại không chứng minh violating directions có measure zero. Nếu không có proof, mô tả đúng là observations về các trajectory đã thử.

Nguồn: D6 §§39–41, A §§72–91, B §§92–101, C §§102–110.

## 7. Query — đóng protocol và chạy lại external evidence

**Câu chuyện chính:** summary nào đủ cho query nào, và semantic mismatch gây decision regret ra sao khi kiểm soát information budget và cùng state panel.

**Hiện trạng:** formal sufficiency/necessity và synthetic transfer có giá trị. Protocol v4 đã sửa nhiều semantics nhưng sửa code chưa tạo external evidence mới; v2/v3 không nên dùng cho kết luận hiện hành.

**Việc tiếp theo:**

1. Chọn phạm vi external nhỏ nhưng native: physical intervention với clone/restore và full-joint receipt; communication query trong environment/policy có message deletion/delay thật. Freeze registered method-query matrix và state panel trước khi chạy.
2. Smoke-test nondegeneracy, population width, budget accounting, full requested/executed action và estimand one-step hoặc continuation có policy cố định. Dùng calibration panel riêng để chọn protocol; không chọn test states vì kết quả đẹp.
3. Chạy v4 với matrices full-information và matched-budget riêng; report regret và Top-k denominators riêng, blocked/degenerate/tied status rõ. Paired comparisons dùng cùng states/seeds thích hợp. Không đòi mọi method phải thắng; cần đo đúng mức và dạng transfer.
4. Audit thêm sự khác nhau giữa **không đủ thông tin để bảo đảm correctness** và **không thể đo regret**. Query §46 chỉ cho số ở cell semantically eligible, nhưng câu hỏi transfer cần quan sát cả summary insufficient. Nếu method executable và target oracle hợp lệ, có thể báo regret như diagnostic kèm nhãn INSUFFICIENT; đừng lọc mất đúng failures paper muốn đo. BLOCKED do thiếu intervention authority là trường hợp khác.

**Cổng hoàn tất:** có complete preregistered matrix trong phạm vi công bố, native providers, nondegenerate targets và matched-budget results. Nếu bị chặn ở native capabilities, thu hẹp rõ phạm vi paper hoặc hoãn external claim; không chèn proxy vào ô trống.

**Dừng:** chữa all-zero CityFlow bằng metric đẹp; coi CybORG BLOCKED là transfer result; xây thêm query-conditioned neural head trước khi benchmark hợp lệ.

Nguồn: Query §§42–69; `SEMANTIC_AUDIT_RESPONSE_20260905.md`.

## 8. Thứ tự triển khai đề xuất

Đây là thứ tự làm việc, không phải cam kết thời lượng thí nghiệm.

| Giai đoạn | Đầu ra cần có | Quyết định sau đó |
|---|---|---|
| 1: sửa trạng thái khoa học | Manifest D6 B/C; Support three-world witness; D6 upper-bound corollary và miền conjecture | Không cấp nguồn lực cho target sai hoặc claim thiếu artifact. |
| 2: chốt manuscript core | Draft Functional và Structural; contribution boundary sáu paper | Đưa hai paper này vào vòng phản biện nội bộ trước. |
| 3: một phép thử quyết định mỗi hướng | Functional fixed-confidence; Structural K-menu benchmark; MASTER Γ_box held-out; Query v4 pilot; D6 symbolic m=6 | Mỗi paper có tiêu chí tiến tiếp/thu hẹp cụ thể. |
| 4: mở rộng có điều kiện | MASTER statistical contract, Query full matrix, Support structure theorem, D6 general-m | Chỉ làm nhánh đã vượt cổng nhỏ trước đó. |

Với nguồn lực một người, dành phần lớn thời gian cho Functional/Structural; MASTER dùng chung statistical/measurement infrastructure với Functional. Support và D6 chỉ nhận các đợt làm có mục tiêu và giới hạn; Query được nâng ưu tiên ngay khi pilot chứng minh adapter và target thực sự dùng được.

**Ranh giới đóng góp:** Functional sở hữu response-to-certificate geometry; Structural sở hữu ranking-menu complexity; MASTER sở hữu typed evidence composition; Support nếu độc lập phải sở hữu structural decision-sufficient support acquisition; D6 sở hữu decision interaction bounds/sharpness; Query sở hữu sufficiency/transfer semantics và benchmark. Dùng chung hạ tầng không có nghĩa dùng một thí nghiệm làm bằng chứng cho sáu headline.

## 9. Tài liệu và mức kiểm tra

Đã đối chiếu sáu individual PDF, các addendum `.tex` gồm D6 B/C, README/provenance ledger, semantic audit, headline summary artifacts và source Lean Partial Test Cover. Đã xem các trang PDF chính tương ứng addenda. Không tái chạy training, solver campaigns hay toàn bộ Lean build. Những con số từ artifact được gọi đúng là artifact-reported; hai scope checks Support/m=2 có tính toán hữu tỉ độc lập.

Nguồn thư mục: `/Users/phanan/Downloads/CIG_AMF_EVOLUTION_REPORTS_APPEND_ONLY_20260905_DELIVERY/`.

Các tài liệu ngoài được kiểm tra có phạm vi hẹp, chưa là systematic firstness audit:

- Howard et al., *Time-uniform, nonparametric, nonasymptotic confidence sequences*: nền tảng cho interval có hiệu lực đồng thời theo thời gian; không tự cung cấp CIG observation assumptions. https://arxiv.org/abs/1810.08240
- Disser et al., *Incremental Maximization via Continuization*: đối chiếu bài toán một growing solution qua nhiều cardinality; chưa kết luận prefix-menu object là mới. https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.47

Script đi kèm `verify_scope_checks.py` kiểm tra witness Support và instance m=2 bằng `fractions.Fraction`. Chứng minh upper bound/supremum m=2 nằm trong phần 6; script kiểm tra số học hữu hạn, không thay thế chứng minh tổng quát hoặc Lean.
