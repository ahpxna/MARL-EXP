# Rà soát: đã làm nhưng chưa đúng kế hoạch — 2026-09-24

Nguồn kế hoạch được đối chiếu:

- `research/papers/THREE_PAPERS_TO_REVIEWER_20260923.md` (gọi tắt là **spec**, số mục §);
- `/tmp/cig_math_blueprints/00–07` (gọi tắt là **bp**);
- `AGENTS.md` (quy tắc audit kết quả ↔ thuật toán);
- `research/papers/ROADMAP.md`.

Đối chiếu với toàn bộ việc đã làm trong phiên (A7 → A-core, B endpoint, C figures, manuscript,
claim map).

Phân loại mỗi mục:

- **ROUTE** — đạt đích nhưng đi đường khác kế hoạch;
- **SCOPE** — phát biểu hẹp hơn kế hoạch yêu cầu;
- **SUBST** — làm một thứ thay cho thứ kế hoạch yêu cầu;
- **FORM** — sai hình thức hoặc quy trình;
- **OPEN** — kế hoạch yêu cầu nhưng chưa làm.

Cột "Hệ quả" cho biết claim nào bị ảnh hưởng. "Sửa" là việc cần làm.

---

## Paper A

| # | Loại | Kế hoạch nói | Đã làm | Hệ quả | Sửa |
|---|---|---|---|---|---|
| A-1 | SUBST | bp02 §9: learner lý tưởng phải là một thuật toán **cài đặt được**: ε-net có weight floor `κ_j→0`, mỗi QP vùng giải tới khoảng primal–dual **có chứng chỉ** `δ_j→0` (rational/verified arithmetic). Oracle nhanh hiện tại chỉ là bản tăng tốc có cùng hợp đồng bracket. spec §A.5: "ideal certified-refinement implementation", có fallback "unresolved". | `idealLearner` là **đối tượng toán học**: `Jval` và GLR là infimum **chính xác** trên tập vô hạn, không có solver, không có `δ_j`, không có weight floor. Nó refresh và kiểm stop **mỗi vòng**, trong khi code refresh mỗi 200 và kiểm mỗi 50. | `ideal_family_finish` đúng cho đối tượng đó, nhưng chưa phải "implementation" theo nghĩa spec. Nhãn "IDEAL" đã có trong ROADMAP, THEOREM_MAP và paper A. | Hoặc (a) giữ nguyên và viết rõ trong paper là "mathematical ideal learner, not an implementation"; hoặc (b) thêm tầng certified-refinement theo bp02 §9 và chứng minh sai số `δ_j` hấp thụ vào η. |
| A-2 | OPEN | bp02 §0 và spec §A.5: hai theorem tách bạch, **(I) finite numerical slack cho code hiện tại** và (II) exact Γ. | Chỉ có (II). (I) chưa làm: chưa có hợp đồng sai số đều, chưa có ổn định đáp án dưới hợp đồng, chưa có stopping-gap bound. | Learner Python chỉ được báo cáo là finite-panel. Paper A đã ghi rõ. | Làm (I), hoặc giữ nhãn finite-panel như hiện tại. |
| A-3 | ROUTE | spec §A.4 bước 7 và §0 file 2: đi qua `LeanPaperACertificatePerturbationV1` (có box B), "take infima and join tracking/selection". | Chuỗi cuối **không dùng** module này. Thay vào đó dùng đường **không cần box**: `LeanPaperA7SqrtLipV1`, `LeanPaperA7DirectFreeV1` (Minkowski, ridge factor, raw-mean perturbation). | Kết quả mạnh hơn (không cần box). Nhưng module spec giao vẫn chỉ compile, không nằm trên đường headline. Paper A vẫn trích `sInf_Qstat_ge`/`perturbationCost_div_le` là "last link of the abstract chain". | Ghi trong paper là chuỗi cuối dùng đường box-free; `CertificatePerturbation` là kết quả phụ của chuỗi trừu tượng. |
| A-4 | ROUTE | bp02 §3 và bp06: selection của code là "first kept" với margin `2Lr+NUM_TOL`; "prove rule thực hoặc đổi code+provenance; không diễn giải thành algorithm khác". | Learner lý tưởng dùng **first-argmax chung** trên (answer × net), không có bước keep-set. | Hợp lệ vì đây là theorem (II) cho một thuật toán khác, có ghi nhãn. Tuy vậy, selection rule của code (A5.3) vẫn **chưa được chứng minh**. | Nếu làm (I) thì phải chứng minh selection rule thật của code. |
| A-5 | FORM | spec §6: sau khi join xong phải viết lại **một lần cho mạch lạc**, "not another historical addendum". Giữ 3–4 headline mỗi paper; chuyển chi tiết Lean vào supplement. | Mình **chèn thêm** một đoạn "The ideal learner, end to end" cùng NOTEPAR và leanbox. | **Mâu thuẫn nội bộ**: intro §"What is new" vẫn viết "the fifth link ... is not claimed as proved end to end ... joining the tail bound to a hitting time that may be infinite, are open". Abstract không nhắc gì tới learner lý tưởng. | Viết lại abstract, intro và đoạn "contribution chain" cho khớp headline A-H4′. |
| A-6 | SUBST | spec §5 **A-F1**: khoảng **có chứng chỉ** cho Γ_true/Γ_proxy từ một tính toán số true-game **có centring và mọi vùng**, lưu primal witness, dual/prior upper, residual, failures, metadata. | Panel trái của `paperA_mechanism.pdf` lấy **cận dưới** từ lower certificate đã lưu (bỏ centring, nên bảo thủ) và **cận trên từ theorem**. Không có tính toán số mới, không có primal witness, không có dual upper. | Khoảng vẫn đúng (cận dưới hợp lệ, cận trên là theorem), nhưng không phải artifact spec yêu cầu. Caption đã ghi rõ. | Cần một producer mới có model (centring, mọi vùng, primal + dual) nếu muốn đúng A-F1. |
| A-7 | SUBST | spec §5 **A-F2**: middle-cell share và **certificate-rate/RMST theo budget**. | Vẽ RMST và share **theo r** ở **một budget** (60000). JSON có `tau_per_run` nên vẽ được `P(τ≤b)` và `E[min(τ,b)]` theo b mà **không cần chạy lại**. | Thiếu đúng trục spec yêu cầu. | Thêm panel "certificate rate and RMST vs budget b" từ `tau_per_run`. |
| A-8 | OPEN | spec §5 **A-F3**: panel mới có swapped truths, hai chế độ gap, active-region transition, 50–100 replicate, log đầy đủ. | Chưa làm (cần chạy mẫu mới). | — | Cần duyệt để chạy producer mới với output path mới. |
| A-9 | SCOPE | spec §8.7: "Read the completed A mechanism/A7 reruns and test each claimed behavior from raw records." | Audit mechanism phát hiện điều kiện stop chỉ chứng nhận đáp án A: đây là chẩn đoán phân bổ, không phải learner. Đã ghi nhãn trong caption và provenance. Chưa audit lại A7 learner trong phiên này. | Panel mechanism không được đọc là "learner học đáp án". | Đã sửa nhãn. |
| A-10 | OPEN | A6 (ROADMAP, abstract A): sample-complexity separation cần bound đếm cumulative-exploration **cho learner surrogate cụ thể**. | Chưa làm. User đã giao ngày 24/9. | Abstract A ghi "claims no separation of sample complexity". Nếu A6 xong thì abstract phải đổi. | Đang làm tiếp. |

## Paper B

| # | Loại | Kế hoạch nói | Đã làm | Hệ quả | Sửa |
|---|---|---|---|---|---|
| B-1 | SUBST | spec §B.5: "designate a measurable fallback when tests disagree ... **the implementation and theorem must name the same one**." | Code Python trả −1 (tính là sai); Lean trả world mặc định. Không sửa code, không chạy lại. Thay vào đó chứng minh `lean_wrong_imp_py_wrong` và ghi provenance: count của script là **cận trên bảo thủ**. | Các budget identification đã chứng nhận upper **chuyển được** sang decoder Lean, nhưng dữ liệu không phải phép đo của decoder đó. Bracket dưới (CP lower) chỉ đúng cho rule của script. | Hoặc đổi code sang cùng fallback rồi chạy **artifact mới** (spec cho phép khi algorithm đổi), hoặc giữ nhãn hiện tại. |
| B-2 | SCOPE | spec §B.3: stopped transcript với stopping time tổng quát, "extend to the stopped transcript with the required limit/data-processing theorem; if E τ infinite, bound automatic; handle finite case". | Lớp policy của `parity_tip_finish` là **finite horizon** (stopping time bị chặn). | Cận dưới chưa phủ policy có τ không bị chặn mà vẫn hữu hạn a.s. | Thêm bước giới hạn `n→∞` (monotone convergence như phía A) để mở rộng tới mọi τ có `E τ < ∞`. |
| B-3 | FORM | spec §6: mạch B phải đi theo: safe-decision geometry → query class → per-query info → adaptive lower + upper → same-channel separation → boundary. Viết lại mạch lạc. | Theorem endpoint (`thm:endpoint`) được **chèn** thành subsection gần cuối. Headline family trong abstract và §family vẫn là họ raw-F `F_{u,v}` (còn open), còn kết quả đã đóng nằm trên kênh parity. | Người đọc thấy headline là họ còn open, kết quả thật lại ở phụ. | Viết lại để kênh parity là mạch chính, còn `F_{u,v}` là phần boundary/tiếp theo. |
| B-4 | OPEN | spec §5 B-F1: nếu cần claim mạnh hơn thì bổ sung ô `m=4` cho identification. | Không làm (không cần cho claim hiện tại). | — | Chỉ làm nếu muốn đường cong rate thực nghiệm. |

## Paper C

| # | Loại | Kế hoạch nói | Đã làm | Hệ quả | Sửa |
|---|---|---|---|---|---|
| C-1 | FORM | spec §6: viết lại mạch lạc; mạch C là ranking → marginal constraint → zero-band prices và endpoint laws → frontier chẵn / breakpoint lẻ → flow equivalence → robustness. | Chèn NOTEPAR, theorem ổn định vật lý, hai figure* và sửa Limitations. Nhiều NOTEPAR lịch sử vẫn còn (ví dụ "An earlier version ..."). | Nội dung đúng, nhưng thân bài vẫn mang lịch sử sửa chữa. | Viết lại một lần. |
| C-2 | SCOPE (đã sửa) | bp04, spec §4: không suy từ cận dưới ra điều về giá thật. | `LeanPaperCCollapseV1` (docstring) và THEOREM_MAP C-H4 viết như thể **giá** là `Θ(min(m,1/ε))`, trong khi định lý chỉ nói về **biểu thức floor**. | Claim quá mức về collapse scale của giá. | **Đã sửa ngày 24/9**: docstring và C-H4 nay nói về floor. File Lean đổi comment sau khi full gate đã freeze, nên sẽ hiện drift. |
| C-3 | OPEN | spec §5 C-F3 (tùy chọn): benchmark thời gian LP permutation vs flow. | Chưa làm. | Không được claim tăng tốc tính toán. Paper hiện chỉ nói về kích thước. | Chỉ làm nếu hiệu năng là đóng góp. |

## Chung cho cả ba paper

| # | Loại | Kế hoạch nói | Đã làm | Sửa |
|---|---|---|---|---|
| X-1 | FORM | spec §6: **claim map** mỗi paper có đúng các cột: scientific claim · model/quantifiers · mathematical proof · Lean declaration · remaining assumptions · algorithm/producer · immutable artifact · figure · **nearest prior art**. | THEOREM_MAP có bảng "State on 2026-09-24", nhưng **thiếu các cột** mathematical proof, algorithm/producer, figure và **nearest prior art**. | Dựng lại claim map đúng 9 cột. Cột prior art lấy từ kết quả của researcher (xem `novelty_briefs_20260924/`). |
| X-2 | FORM | bp06: mỗi headline kèm **proof hash**. | Chưa ghi hash vào claim map (hash nằm ở `report/SOURCES.sha256` của gate). | Sau khi `full3_20260924_ideal` xong, chép hash module vào claim map. |
| X-3 | OPEN | spec §8.8: kiểm scope, format và policy của **venue thực** từ hướng dẫn chính thức. | Chưa làm. | Làm trước khi đóng gói. |
| X-4 | OPEN | spec §7: novelty so theo **định lý**, đọc nguồn gốc. | `literature_audit_20260921` mới lọc **abstract** được 240/1000 bài, chưa đọc toàn văn. | Giao researcher theo `novelty_briefs_20260924/`. |
| X-5 | FORM | Quy trình: không sửa nguồn sau khi gate đã freeze. | Đã sửa **comment** của `LeanPaperCCollapseV1` trong lúc `full3` đang chạy. Verdict vẫn áp dụng cho bytes đã freeze; report sẽ ghi drift. | Chạy gate lại sau khi viết lại manuscript. |
| X-6 | FORM | Quy trình (memory): smoke trước, long run sau. | Đã tuân thủ: smoke PASS rồi mới full. Nhưng ROADMAP có một lúc ghi "smoke gate …" trước khi smoke pass. Đã sửa. | — |

---

## Bổ sung: đối chiếu với kế hoạch và câu chuyện đã chốt trong phiên Codex

Nguồn: phiên giám sát `chatgpt.com/s/cx_6ab532c81d708191a1dd3665f41b9813`, đọc từ dưới lên.
Các đoạn liên quan là: "Có: đóng đúng các mắt nối …" (chốt câu chuyện và kế hoạch
experiment), "Còn nợ, và không chỉ là lỗi compile …" (audit code–JSON), và ước lượng 60%.

**Câu chuyện đã chốt.** Ba kết quả về *cái giá của việc giải sai bài toán trung gian*:

- **A** — tối ưu sai oracle. Lõi novelty là separation sau khi tối ưu, starvation và
  frontier `F(β)=Θ(β/rM)`.
- **B** — phân biệt nhiều world hơn cần thiết. Lõi là luật `s_safe`/`s_id` gộp geometry của
  đáp án an toàn với bậc quan sát, có cận dưới adaptive và decoder đạt bậc.
- **C** — tối ưu một phân phối ranking nhưng đánh giá sai cách nó được dùng. Kể thành "hai
  cách mất một hệ số tuyến tính": thêm ràng buộc marginal, và max E so với E max.

| # | Loại | Kế hoạch Codex nói | Hiện trạng | Sửa |
|---|---|---|---|---|
| P-1 | SCOPE (rò thông tin, nặng) | Experiment A: "Dùng cùng stopping certificate cho **quyết định thật** ở các policy **deployable** … không để baseline dừng bằng certificate yếu hơn"; AGENTS.md cấm nhãn ẩn đi vào learner. | `EXP_paperA_mechanism.py` dừng khi `lo > thr and ans == "A"`, với certificate chỉ dựng cho đáp án A. **Nhãn đáp án thật đã đi vào luật dừng.** Các rule không phải learner deployable. Đã ghi nhãn "allocation diagnostic" (provenance addendum, caption A). | A-F2 đúng spec cần **artifact mới**: certificate hai đáp án như panel swap, dùng chung cho mọi rule. Cần duyệt để chạy. |
| P-2 | SUBST | Experiment A: producer theo `(r,M)`, so **true-oracle learner**, **frozen-proxy learner có exploration** và uniform; đảo nhãn arm và tie-break; log counts từng cell, bracket, stopping lower bound, wall time; pilot rồi khóa cấu hình, khoảng 200 paired trajectories. | Chưa có. Rule "geometry" hiện là Nelder–Mead trên A-certificate, không phải true-oracle learner. Mới 24 run mỗi rule, không có pilot hay khóa cấu hình. | Producer mới, output path mới (cần duyệt). |
| P-3 | SUBST | "Hai đồ thị cần nhất: `t ↦ N_middle(t)/t` và `policy ↦ E[min(τ,B)]`." | Mình vẽ middle share **cuối** theo r. JSON có `traces`, nhưng chỉ cho run đầu mỗi rule. | Vẽ `t ↦ N_mid(t)/t` từ `traces` (ghi rõ là một quỹ đạo), cùng RMST theo budget (mục A-7). |
| P-4 | OPEN (câu chuyện) | Paper C: "hai cách mất hệ số tuyến tính", dùng `V_path/V_avg = m−1` của Structural (Lean: `avg_lower`, `path_lower`, `avg_achieved`, `path_achieved` trong `LeanStructuralFamilyLowerV1`). Figure C3: max E vs E max. | Paper C ghi "no result here is claimed for" `E max_k r_k`. Spec 23/9 cũng không đòi phần này. | **Cần quyết định**: đưa vào C (kết quả đã có Lean, không cần toán mới) hay giữ ngoài. Nếu đưa vào thì không được nhân hai hệ số thành `m²`: bài toán kết hợp chưa được giải. |
| P-5 | SCOPE | B: headline là **luật tổng quát** `N*_safe = Θ(h^{-2 s_safe} log 1/δ)`, `N*_id = Θ(h^{-2 s_id} log 1/δ)`. | Đã chứng minh: nửa tổ hợp của luật (`safeAt_iff`, …) và **một instance** trên kênh parity (`parity_tip_finish`). Luật sample-complexity cho họ tùy ý chưa chứng minh; spec nói không bắt buộc. | Manuscript không được phát biểu luật tổng quát như một định lý. Chỉ nói "nửa tổ hợp: theorem; rate: trên hai instantiation". |
| P-6 | OPEN (nâng cấp) | A6 `Ω(log²(1/α))` vs `O(log(1/α))`: "rất mạnh nếu nối đúng policy; nếu worker đã làm thì đưa lên headline". | Chưa làm (đang làm, mục A-10). | Nếu xong: sửa abstract A ("claims no separation of sample complexity"). |
| P-7 | OPEN (nâng cấp) | B: lớp query `Q_η`, `sup KL ≍ h⁶ + η²h⁴`, pha chuyển tại `η ≍ h`. | Chưa làm. Artifact chỉ có một probe. | Tùy chọn. Không dùng đường cong một probe thay cho theorem. |
| P-8 | FORM | "Viết main text từ kết quả cuối; lịch sử thuộc ledger" và "related work theo theorem: *họ đã chứng minh X; ở đây thêm Y dưới model Z*". | Chưa. Related work vẫn theo chủ đề; chỉ có bảng "Which of our theorems does not follow". | Làm sau khi có kết quả của researcher. |

Các mục Codex bắt ở lượt "60%" đã được xử lý trước phiên này và mình kiểm lại trên bản hiện
tại: caption B chỉ còn `0.05/(2J)`; abstract C không còn nói flat ranking đạt free value;
abstract A không còn viết "only the extrema may move"; gate đã lấy transitive closure của
import.

---

## Tóm tắt ưu tiên

1. **Nhất quán manuscript** (A-5, B-3, C-1, X-1, P-5, P-8): phải làm trước khi đưa
   reviewer. Hiện có mâu thuẫn nội bộ ở A.
2. **Rò thông tin trong luật dừng của thí nghiệm mechanism** (P-1): đã ghi nhãn. Nhưng A-F2
   đúng nghĩa cần chạy lại với certificate hai đáp án.
3. **Hình theo đúng spec** từ dữ liệu có sẵn: A-7 và P-3 (vẽ lại được, không cần chạy lại).
4. **Câu chuyện C** (P-4): quyết định có đưa max E vs E max (đã có Lean) vào C hay không.
5. **Phạm vi còn hẹp**: B-2 (finite horizon → mọi τ có `E τ < ∞`); A-2 (theorem I).
6. **Cần quyết định trước khi chạy tính toán mới**: A-1(b), A-6, A-8, B-1, P-1, P-2.
7. **Nâng cấp**: A6 / P-6 (đang làm); P-7 (tùy chọn).
8. **Novelty**: X-4, giao researcher theo `novelty_briefs_20260924/`.

## Cập nhật 2026-09-24, chiều

| # | Trạng thái mới | Việc đã làm | Còn lại |
|---|---|---|---|
| A-10 / P-6 | **ĐÓNG MỘT PHẦN (oracle-allocation)** | `LeanPaperA6SurrogateCostV1`: learner bám một optimum chính xác bất kỳ của surrogate đóng băng (warm start, forcing `1/√(s+1)`, `argmax(s w⋆ − N)`, GLR stop thật) có `E τ_δ ≥ (KM/8)² log²(1/δ)`; learner lý tưởng `O(log(1/δ))`; tỉ số không bị chặn (`surrogate_vs_ideal`). Giả thiết thỏa được (`surrogate_optimum_exists`, `wUnifC`). Abstract A và đoạn mới trong paper A đã sửa, ghi rõ phạm vi. | Design là optimum của surrogate **tại world thật** (true extrema vào allocation). Learner tính lại surrogate tại ước lượng vẫn chưa có. |
| X-2 | **ĐÓNG cho full3** | Bảng hash theo headline trong `THEOREM_MAP.md` ("Proof hashes"), lấy từ `report/MODULES.tsv` của `full3_20260924_ideal` (VERIFY PASS, 188 module, 1505 định lý). | Hash của 3 module A6 lấy từ smoke gate `smokeA6_20260924`. |
| A-7 / P-3 | **ĐÓNG (từ dữ liệu có sẵn)** | `paperA_budget.pdf` (`FIG_paperA_budget.py`, 5/5): `P(τ≤b)` và `E[min(τ,b)]` theo budget từ `tau_per_run`; `N_mid(t)/t` từ `traces` (chỉ run đầu, có ghi rõ). Đã đưa vào paper A (`fig:abudget`). Audit phát hiện rule proxy là **oracle allocation** (`w_proxy` = extrema của world thật): đã sửa bằng addendum 2 của provenance note, không sửa văn bản cũ. | Panel vẫn là chẩn đoán phân bổ (P-1 chưa giải quyết). |
| A-5 | **ĐÓNG một phần** | Intro (chuỗi đóng góp, mục 5–6), Limitations 3 và 6, Conclusion, NOTEPAR cũ trong paper A đã khớp với A-H4′/A-H5′. | Chưa viết lại toàn bộ paper một lần (spec §6). |
| B-2 | **ĐÓNG (kênh parity)** | `LeanPaperBStoppedParityV1`: policy dừng không bị chặn (`SPol`), cắt ngắn theo horizon (`trunc_correct`: đúng ở mức `δ+ε`), cận dưới ở mức `2δ` (`stopped_safe_lower`, `stopped_id_lower`, dạng `log(1/δ)`: `stopped_lower_log`); decoder hữu hạn nhúng được (`ofPol_correctS`, `costS_ofPol`), nên lớp không rỗng và phía trên cũng chuyển sang (`stopped_parity_rates`). Không cần Ionescu-Tulcea: một kernel policy dùng cho mọi horizon. | Họ `F_{u,v}` vẫn open. |
| B-3 / P-5 | **ĐÓNG một phần** | Abstract B viết lại: headline là kênh parity (hai rate, mọi policy dừng a.s.), rồi nửa tổ hợp và moment law, `F_{u,v}` là boundary. Intro có đoạn thứ tự đọc; Limitations 1–2 và Conclusion khớp. Luật tổng quát không được phát biểu như định lý. | Chưa đảo thứ tự các section (viết lại một lần theo spec §6). |
| C-1 | **ĐÓNG một phần** | Hai NOTEPAR lỗi thời trong C đã sửa: attainability của `b_k = k mod 2` đã chứng minh (`attainment`, `familyBaselineIdentification_holds`); `V_m(0) = 4/(m(m+4))` chẵn đã chứng minh (`even_value_zero`); bỏ câu 'an earlier draft said so'. | Viết lại một lần. |
| X-1 | **ĐÓNG (trừ cột prior art)** | `CLAIM_MAP_9COL_20260924.md`: đúng 9 cột spec §6 cho A-H1..A-H5′, A-F, B-H5′, B-H1, B-H2/H4, B-D, C-H1′..C-H4′, kèm hash artifact. Mọi tên Lean, script, JSON đã kiểm là tồn tại. | Cột nearest prior art chỉ là con trỏ tới trích dẫn hiện có và brief; verdict chờ `RESULT_<A|B|C>.md` của researcher. |
| A-10 / P-6 (tiếp) | **ĐÓNG** | Learner deployable: re-solve surrogate tại ước lượng mỗi vòng (`surOracle`, hoặc bất kỳ oracle trả optimum chính xác). `E τ_δ ≥ (KM/8)² log²(1/δ)` (`est_cost_log_sq`, `surrogate_learner_cost`, `exact_oracle_cost`), tỉ số với learner lý tưởng không bị chặn (`surrogate_learner_vs_ideal`). Oracle chỉ thấy ước lượng; số vòng ước lượng sai có kỳ vọng `≤ s₀+2` (`badAll_expect`, Ville). Paper A (abstract, intro mục 6, đoạn mới, Limitations 6, Conclusion) đã sửa. | `δ₀` rất nhỏ; chỉ một họ và một tốc độ forcing. Smoke gate `smokeA6est_20260924` đang chạy. |
| B-1 | **ĐÓNG** | Chạy lại có ghép cặp: `EXP_paperB_decoder_leanfallback.py` (script mới, không sửa producer cũ) dùng fallback của decoder Lean, cùng seed và cùng chuỗi draw. Kiểm tra ghép cặp đạt: 308/308 count safe trùng khớp; mọi count identification ≤ count cũ (`lean_wrong_imp_py_wrong` trên dữ liệu), bớt 13.831 lỗi. Ở mức family-wise đã sửa, không budget chứng nhận nào đổi, nên budget identification là của decoder Lean. Paper B và provenance note đã cập nhật; JSON cũ giữ nguyên. | — |
| P-1 / A-F2 | **ĐÓNG** | Producer mới `EXP_paperA_deployable.py`: ba learner deployable (oracle chỉ thấy ước lượng), MỘT certificate hai đáp án, world gốc và world đảo. 0/505 run dừng sai; surrogate re-solve tại ước lượng chứng nhận 22/3/0/0 trên 24 run (r = 1/2/4/8) ở world gốc, hai rule kia chứng nhận hết. Hình `paperA_deployable.pdf` (fig:adeploy) và provenance note mới. | α = 0.05 ≫ δ₀: không phải phép thử bậc log². |
| X-5 | **ĐÓNG** | Full gate `full4_20260924` PASS: 196 module, 1547 định lý, không drift, phủ mọi module sau full3. | — |
| P-4 | **ĐÓNG** | Đưa max E vs E max vào paper C, có Lean trên chính objective của C: `LeanPaperCExPostV1` (`pathValue_eq`: `E max_k r_k` có infimum `2/(m+4)` với mọi m ≥ 3; `path_over_free`: tỉ số `m−1`; `objective_le_pathObjective`). Không dùng module Structural (chưa có trong gate); chứng minh trực tiếp bằng bước ±3 và parity. Paper C: abstract, subsection `sec:expost` (Thm `thm:expost`), NOTEPAR, caveat, Limitation 5. | Bài toán ex-post có band chưa giải; không nhân hai hệ số. |
| A-6 / A-F1 | **ĐÓNG** | Producer mới `EXP_paperA_certified_separation.py`: tính true game có centring và MỌI vùng, số hữu tỉ chính xác. Cận trên từ dual của LP trên các alternative đã kiểm chính xác; cận dưới từ dual Lagrange từng vùng (weak duality). Tỉ số Γ_true/Γ_proxy: [0.8372,0.8374], [0.7214,0.7216], [0.5664,0.5667], [0.3982,0.3982] ở r = 1, 2, 4, 8, nằm trong bracket đã chứng minh; ở design tỉ lệ phương sai, cận dưới đúng bằng giá trị của định lý. Hình `paperA_certified.pdf` (fig:acert), provenance note mới. | — |

## Cập nhật 2026-09-25

| # | Trạng thái mới | Việc đã làm | Còn lại |
|---|---|---|---|
| B-2 (tổng quát) | **ĐÓNG cho mọi kênh** | `LeanPaperBStoppedLawV1`: luật obstruction cho mọi policy dừng hầu chắc chắn trên MỌI kênh dạng protocol (`stopped_obstruction_lower`, `_chi`, `_star`, mức `2δ`); `trunc_correct`; `costSt_ofFinite`, `correctSt_ofFinite` (policy horizon hữu hạn là policy dừng cùng cost, nên giả thiết thoả được). Paper B: Theorem `thm:lowerstop`, Limitation 2 viết lại. | Dừng a.s. phải đều trên tập world hữu hạn; hệ số 2 trong δ |
| B-3 / P-5 (tiếp) | **ĐÓNG** | `F_{u,v}` không còn là "boundary": kênh Gaussian của chính họ này được dựng (`LeanPaperBFamilyChannelV1`), cặp v đồng nhất CHÍNH XÁC với iterated difference (`famDens_vdiff`), hai cận dưới thích nghi; decoder với ngân sách `log(1/δ)` (`LeanPaperBFamilyDecoderV1`); cả hai rate cho mọi policy dừng a.s. Paper B: Theorem `thm:famrates`, abstract/results/limitations/conclusion cập nhật; nội dung cũ (Chebyshev, `LeanPaperBHeadlineV1`) GIỮ, ghi là bị thay thế. Supplement: status map cập nhật, thêm build record. | Hằng số đều theo `r` (B3); `famSafe` được phát biểu (đã kiểm khớp với `EXP_paperB_construction`: u=+1 ⇒ mọi đáp án trừ toạ độ 1, u=−1 ⇒ {1}) |
| X-5 (tiếp) | **ĐÓNG** | Full gate `full6_20260925` PASS: 214 module, 1666 định lý, tiên đề chuẩn, không drift (214/214 file frozen trùng byte với bản làm việc). Phủ mọi module mới 2026-09-24/25. | — |
| X-6 (mới) | **ĐÓNG** | Rà trích dẫn theo module: 2 module được supplement trích nhưng CHƯA từng vào gate (`LeanUnifiedObstructionOrderV1` ở B, `LeanUnifiedStructuralRelaxedV1` ở C). Đã thêm vào MODS; smoke gate `smokeUNI_20260925` PASS (2 module, 16 định lý). Build record của supplement A, B, C ghi đúng gate. | Lần full gate sau sẽ phủ cả hai |
| P-2 | **ĐANG CHẠY (launch 3)** | Launch 2 hoàn tất 31/36 ô rồi bị giết cùng phiên terminal (không nohup), KHÔNG ghi dữ liệu từng run (script chỉ ghi JSON ở cuối). Launch 3: thêm checkpoint theo ô (`paperA_deployable_paired.partial.jsonl`, fsync, chỉ resume khi hash config và hash module rule khớp), smoke kiểm resume cho kết quả trùng hệt; chạy bằng nohup. Seed chỉ phụ thuộc (ô, run) nên kết quả trùng launch 2: các ô đầu đã trùng từng số. | Phân tích, hình, provenance note, đưa vào paper A |
| B5 upper | **ĐÓNG** | Giả thiết test của tournament được chứng minh trên MỌI kênh bằng thông tin Hellinger (`LeanPaperBHellingerTestV1`): test tỉ lệ likelihood theo block, sai ≤ BCⁿ ≤ e^{−nκ_H}; luật trên `|W|²⌈log(|W|/δ)/t*_H⌉` không điều kiện; `resolved_le_scale` cho khớp khi KL ≤ Kκ_H; ví dụ Gauss ±1 (BC = e^{−1/2}) chứng tỏ giả thiết không rỗng. Paper B: Theorem `thm:hellupper`, Limitation 1 viết lại, abstract/conclusion không còn nói "minimax Θ(log(1/δ)/t*)" vô điều kiện. | So sánh KL–Hellinger trên kênh parity và họ latent |
| A6 (dilution) | **ĐÓNG phần trải ngân sách** | `LeanPaperASacrificeDiluteV1`: đệm policy δ-đúng π0 bằng 4k truy vấn tối ưu surrogate (round-robin 4 ô A) sau khi quyết định: vẫn δ-đúng, N = N0 + 4k, 8rMD ≤ N·sac ≤ N0·sac(w̄0), sac ≤ N0/(N0+4k). Paper A: Theorem `thm:dilute`, Limitation 2 viết lại (phần còn mở nói rõ). | Xen kẽ trong lúc chạy có hạ được ngân sách dưới N0 không; khoảng hằng số |
| C2 (window) | **ĐÓNG** | `LeanPaperCCollapseWindowV1`: trên cửa sổ (1/2m, 1/m) mọi nhiễu có giá trị dương giữ tỉ số ≥ (m−1)/8; gộp lại ≥ min(m−1, 1/ε)/16 trên toàn 0 < ε ≤ 1/6. Paper C: Theorem `thm:collapse` (b) mở rộng, Limitation 2 bỏ câu "chỉ có envelope floor". | Hằng số hai phía còn khác nhau |
| P-2 | **ĐÓNG** | Launch 3 xong (7695 s, 5/5): 7200 run, 6258 dừng, 0 sai; hình `paperA_deployable_paired.pdf` (7/7, tái hiện đúng 31 ô của launch 2 bị giết); provenance note; paper A Fig. `fig:apaired` + 2 dòng trong bảng evidence. Kiểm thuật toán: rule chỉ thấy ước lượng (hash module rule trùng pilot), cặp theo seed, α kiểm trên mọi run đã chạy, censoring báo riêng và nói rõ là cận dưới. | — |
| Round 2 (2026-09-25) | **ĐÓNG** | B: luật tổng quát chặt hai phía trên cả hai kênh (`LeanPaperBHellingerFamilyV1`, `LeanPaperBHellingerParityV1`); `famSafe` được dẫn ra từ loss (`LeanPaperBFamilySafeV1`). A: luật hy sinh cho policy dừng a.s. (`LeanPaperASacrificeStoppedV1`); A1 thực ra đã có trong Lean (`LeanPaperASeparationV1`, cả hai chiều sau sup theo thiết kế) — tracker ghi sai, đã sửa; A3: chứng chỉ KKT chính xác 81 vùng × 2 họ × 6 giá trị M (`EXP_paperA_frozen_proxy_exact.py`, 7/7). Paper B: Theorem `thm:tight`, sửa câu crossover (chỉ moment, cross term, shape là đã chứng minh). Paper A: `thm:sacstop`, đoạn underpricing, Limitations 1, 4, 5. | Còn mở: A2 (learner cài đặt, độ chính xác hữu hạn), khoảng hằng số của A6, P-7 (tuỳ chọn) |
