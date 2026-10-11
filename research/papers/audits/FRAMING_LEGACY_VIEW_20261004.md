# Chốt framing: Legacy-View Emulation cho fleet MARL trộn phiên bản (04/10/2026, ~00:40 EDT)

Phản hồi review `HISTORY_FRAMING_REVIEW_20261004` (ở `/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/`). Tài liệu này **thay** khẩu hiệu "Histories, Not Formats" trong `STATUS_NOVELTY_STORY_20261003.md` §story. Không mở hướng mới.

## 1. Chấp nhận

| Điểm review | Quyết định |
|---|---|
| A2A có task lifecycle và context continuity; Liskov–Wing có history properties; Abadi–Lamport có refinement mapping | **Chấp nhận.** Bỏ đối lập "A2A = format, ta = lịch sử". Bổ đề Lean mới đúng là một chứng minh kiểu refinement/simulation: đây là công cụ, không phải novelty. |
| Tựa *Upgrading Communication Without Retraining Every Agent: Legacy-View Emulation for Mixed-Version MARL* | **Chấp nhận** làm tựa làm việc. |
| "Lịch sử" phải là **view legacy** mà protocol tạo ra; actor là feed-forward | **Chấp nhận.** Chuỗi chính xác: lịch sử vật lý/hành động → state protocol (cache, bảng relay, age) → view → input → action. Lean định nghĩa đúng `D_i(T_i^U(h_t)) = v_i^K(h_t)`, trong đó `D_i` có tính nhân quả và chỉ đọc state cục bộ cùng packet đã nhận. |
| Giữ nguyên view là điều kiện **đủ**, không cần | **Chấp nhận.** Ghi rõ trong docstring Lean (WHAT THIS DOES NOT ESTABLISH). |
| Fleet trộn: NEW đổi quỹ đạo, nên dựng lại view không bảo đảm return | **Chấp nhận.** Định lý lượng hoá trên mọi quỹ đạo `x`, kể cả quỹ đạo của fleet trộn. Nó cho OLD view K1 **của chính quỹ đạo đó**, không nói gì về return. Return vẫn là endpoint thực nghiệm (E7). |
| Vai trò N4 / emulator +8,13 / E3 / G2 | **Chấp nhận nguyên bảng.** "Exact" chỉ gắn với decoder và phạm vi replay. G2 là ví dụ biên phụ. Rút lại câu "information-preserving transport" về KERNEL_MEAN: chưa chứng minh nó giữ thông tin. |
| "Hơn rollback" chỉ khi kèm chi phí | **Chấp nhận.** Được viết "hiệu năng cao hơn với chi phí truyền lớn hơn" nếu E7 xác nhận. Không viết "thắng cùng chi phí" hay "áp đảo". |

Câu mở đầu dùng theo review: *"A communication upgrade can preserve the packet schema while changing the cached and relayed observations on which a learned receiver relies…"* Không công bố thắng trước khi có report E7.

Bổ sung từ E9c cho câu mở đầu: control `u2table` chính là thiết kế "ngây thơ". Cùng schema 25 B và cùng lịch gửi, sender NEW chỉ đặt bảng relay U2 vào packet. Kết quả: view của receiver cũ lệch ở 400/416 bước-agent, action lệch 39–59 lần/episode (smoke dev 901, seed 0). Đây là minh hoạ cụ thể cho "đúng format nhưng sai view".

## 2. Bốn điều kiện đóng: trạng thái

**(1) Decoder thực sự phân tán.**
- E9b (`MARL_e3_legacy_decoder_eval.py`): mỗi agent chỉ đọc cache/view của chính nó, bảng của sender mà nó đã decode, và lịch legacy công khai.
  - Kiểm bằng đọc code: `merge_views` chỉ đọc `prev[k]` với k là sender được decode trong bước, `never_heard` không vào encoder.
  - Nhưng state vẫn nằm chung một object, và bảng truyền dưới dạng object Python với timestamp đủ chính xác.
- E9c (`MARL_e3_legacy_decoder_nodes_eval.py`):
  - Mỗi node là một object riêng: có bản sao lịch riêng (kiểm mọi bước rằng các bản sao trùng nhau), cache riêng, bảng riêng.
  - Bảng được serialise theo slot với định dạng wire: full; wire4 = age 4 bit bão hoà ở 14, 185 bit; wire5 = age 5 bit bão hoà ở 31, 193 bit ≤ 200, vẫn vừa một gói 25 B.
- Lean (`LeanMarlLegacyViewDecoderV1`): `nodeStep` chỉ nhận protocol công khai, bước, state riêng và các base packet đã nhận. Kiểu của hàm chính là bảo đảm tính cục bộ.

**(2) Bổ đề invariant.** `LeanMarlLegacyViewDecoderV1.lean` compile sạch: 0 error, 0 sorry, chỉ có cảnh báo deprecation. Smoke gate: smokeMARLLEGACY_20261004 (5 module G7 + phụ thuộc, 55 định lý) và smokeMARLLEGACY2_20261004 (module này, 21 định lý) đều **SMOKE PASS**, chỉ dùng axiom chuẩn (propext, Classical.choice, Quot.sound).
- `dec_eq_ref` / `dec_eq_ref_upto`: dưới điều kiện lồng `S_t(i) ⊆ D_t(i)`, cache và bảng của mọi node bằng cache và view K1 tham chiếu ở mọi bước. Bao phủ khởi tạo, cập nhật cache, merge (freshest, so sánh chặt), giới hạn slot, và eviction (bảng dựng lại mỗi bước).
- Age bão hoà: `dec_wire_eq_ref` cho kết quả chính xác với t ≤ c+1. wire5 phủ được episode 26 bước, wire4 thì không. `saturation_can_flip` cho thấy với trường age bão hoà, merge có thể chọn bản relay cũ hơn.
- Tie-breaking: `ref_honest` + `freshest_perm` + `ref_merge_perm` — entry trung thực nên thứ tự duyệt ứng viên không ảnh hưởng kết quả.
- `same_action`: cùng input (mọi hàm của bước và view, kể cả age bão hoà ở 14) dẫn tới cùng action.
- `miss_breaks`: thiếu một packet trong lịch là view lệch ngay, nên điều kiện lồng không rỗng.
- `nesting_satisfiable`: giả thiết thoả được, kể cả khi D chứa S thật sự (lồng nghiêm ngặt).
- Không chứng minh: rằng Python cài đúng mô hình. Bằng chứng cho phần đó là replay từng bước.

**(3) Replay từng bước + đối chứng phá hỏng.**
- E9b-1 (đăng ký trước): **SUPPORTED**. 10/10 seed dev, layout ALL/D/C, 0 lệch ở packets / cache / view / input / action, 0 packet thiếu.
- E9b-2: tới 00:38, 1408/1408 episode panel có queue decoder = E7 EXACT_PROTO_OLD. Còn chờ E9b seed 6–9 và E7.
- E9c smoke (dev 901, seed 0; chưa phải bằng chứng):

  | Biến thể | Kết quả | Ý nghĩa |
  |---|---|---|
  | full / wire4 / wire5 | 0 lệch ở mọi phần | — |
  | `relay_needed` | 628 | bảng relay thật sự cần |
  | ages | view lệch 286, action lệch 0–4 | phát hiện được |
  | empty | view lệch 286, action lệch 16–23 | phát hiện được |
  | u2table | view lệch 400, action lệch 39–59 | phát hiện được |
  | stale | lệch 416 ở mọi phần | phát hiện được |

- Bài học thiết kế: bản đối chứng đầu tiên chỉ làm cũ entry mới nhất. Nó cho **0** lệch, vì dưới lịch age-first chung entry đó luôn đã có trong cache của receiver. Đối chứng phải được chọn sao cho chắc chắn tác động vào view, nếu không thì "0 lệch" không chứng minh được bước kiểm có khả năng bắt lỗi.
- E9c đầy đủ (dev + panel, 10 seed) đã đăng ký và đang xếp hàng sau E9b.

**(4) Chi phí E9** (mỗi episode, panel E7):

| Kênh | Packet giao | Broadcast riêng |
|---|---|---|
| U2 | 3 123 (78 075 B) | 376 (9 400 B) |
| Base packet thêm | 416 decode bởi **cả 16 agent** (10 400 B, +13,3 %) | 52 (1 300 B, +13,8 % airtime) |
| Rollback K1 | 416 | 52 |

- Mỗi node decode thêm đúng 1 base packet mỗi bước (`decoded_eq_sched`).
- Agent NEW bắt buộc giữ state legacy: control `u2table` cho thấy bỏ state đó thì view của OLD hỏng.
- Khai báo thẳng: base packet là **dung lượng trả thêm** ngoài U2, không lấy từ ngân sách U2.
- Dòng chi phí EXACT_PROTO trong report E7 (208 decode, chỉ tính OLD) bị thay bằng con số tính cho mọi agent.

**Cách cập nhật thay thế không tốn byte thêm** (review mục 4): emulator phía receiver EMU_OLD (E6/P2).
- Nó dùng mirror của lịch legacy để biết K1 sẽ giữ bản sao nào, rồi tìm bản sao đó trong lưu lượng U2.
- 0 byte thêm, khớp K1 trên dev (E6), nhưng **không có bảo đảm**: P2 ghi nhận các ca hiếm bản sao legacy không bao giờ tới (traffic 5407).
- E7 so sánh trực tiếp EMU_OLD (0 B) với EXACT_PROTO_OLD (có định lý, +1 300 B broadcast). Đây là một trade-off nên báo cả hai, không chọn hộ người đọc.

## 3. Còn mở (theo thứ tự)

1. **E7.** Đọc theo 3 endpoint đã đăng ký: P-a EMU_OLD − FB_OLD; P-b EMU_OLD − U2/PLAIN; P-c NEW non-inferiority vs U1/PLAIN với biên 0,5. Báo FBR_OLD, FT/PCT (tham chiếu được phép cập nhật), rollback (tham chiếu tốn ít tài nguyên nhất) kèm vector chi phí ở trên.
2. **E9b-2 và E9c đầy đủ** → `e3_wave_20261003/e9_report.txt` (reporter `scripts/MARL_e3_e9_report.py`, viết trước khi có kết quả).
3. ~~Smoke gate Lean~~ — xong, SMOKE PASS (04/10 00:43 và 00:44).
4. Viết claim sau khi có xác nhận. Dạng được phép: "hiệu năng hệ thống cao hơn ở cùng ngân sách kênh nâng cấp mà không đổi trọng số receiver bị khoá, với chi phí +X" — chỉ khi đo được.
5. Một benchmark ngoài để kiểm tính chuyển giao (NYC cần máy ≥ 32 GB; P3 cần quyền tải).

## 4. Ghi chú wave 2b (E2/E10), cùng đợt

- E10: **NO-GO** theo đúng quy tắc đã đăng ký.
  - V2D − FTMIX ở L5 = [+0,20, +2,10]: không đạt > +1 trên cả hai seed.
  - V2D − PCT = [−0,53, +1,48].
  - Old drop của V2D = [0,75, 1,00], vượt ngưỡng 0,5.
- E2:
  - "Policy nào dẫn quỹ đạo paired": OP − A0 > 0 ở mọi mức trên cả hai seed (L1 +10,65/+1,31 … L10 +0,49/+7,11).
  - Old-data occupancy FTMIX − SI phần lớn > 0.
  - h-weighting (PAIRED − UNI) không nhất quán.
- **Post-hoc, chưa đăng ký:** OP hơn FT-mix ở L5 trên cả hai seed dev (+1,65, +3,19), old drop 0,98/0,50. Chỉ là gợi ý cho tham chiếu "được phép cập nhật", không phải kết quả, và không mở hướng mới.

## 5. Cập nhật 04/10 05:37 — trạng thái sau E7 / E9 / E12 / E13 / E14 (thay mục 3 "Còn mở"; các mục trên giữ nguyên làm lịch sử)

**Các kết quả đã đóng** (ledger MARL L-328, L-330, L-331; báo cáo E7 / E13 ở `w2/`):

| Kết quả | Nội dung |
|---|---|
| **E7** (đăng ký trước) | P-a EMU_OLD − FB_OLD: +3.15 [2.24, 4.07] (D), +3.28 [2.06, 4.58] (C). P-b, P-c SUPPORTED. EMU − FT +0.32 và EMU − PCT +0.56 có CI chứa 0: **chưa phát hiện khác biệt; KHÔNG phải tương đương**. |
| **E9** (decoder base-packet, chính xác theo định lý dưới nesting) | 2560/2560 episode panel bằng nhau; wire4 0 lệch trên 2800 episode. Chi phí: +1 300 B unique / +10 400 B decoded mỗi episode. |
| **E12** (emulator 0 byte; L-330) | View bằng nhau ⇔ coverage, 0 ngoại lệ trên 532 480 OLD agent-step. Coverage hỏng ở 3.8e-5 số agent-step (20 ca, đều lớp `never`, đều ở t = 15). P(action lệch \| hỏng) = 0.15. Lean E12-a: `LeanMarlPacketEmulatorV1` (`emu_eq_ref_iff`, `emu_older_iff`, `fresh_not_necessary`, `dishonest_breaks`; giả thiết được chứng minh thỏa được). |
| **E13** | Per-agent: 0/8 OLD agent "tệ hơn có ý nghĩa với biên −0.5". Nhưng cả 8 ước lượng điểm đều âm, và **non-inferiority theo từng agent THẤT BẠI**: cận dưới Bonferroni của agent 8 là −9.43 % (D), −12.86 % (C). Cách đọc đúng: CI rộng chưa loại trừ mức hại đó; không phải bằng chứng hại thật 9–13 %. |
| **E14** (L-331) | OP − FTMIX = +0.36 [−0.17, +0.93]: NOT SUPPORTED. FT-mix / PCT vẫn là tham chiếu được phép cập nhật. |

**Câu chữ bắt buộc trong bản thảo:**
- Hai cách cài đặt cùng một hợp đồng legacy-view:
  - base-packet decoder: có byte, chính xác theo định lý;
  - emulator 0 byte: chính xác ⇔ coverage, mà coverage là thuộc tính của realisation kênh, đo được.
- Cả hai đảm bảo **view** trên CÙNG quỹ đạo vật lý. Không đảm bảo return của OLD trong fleet trộn, vì NEW đổi thế giới mà OLD sống trong đó (E13).
- Không viết "OLD agents are protected".
- Viết: "no OLD agent was significantly worse than all-OLD by more than 0.5; per-agent non-inferiority was not established".
- So với rollback phải nêu chi phí: kênh nâng cấp 78 058 B/ep, rollback 10 400 B/ep.

**Còn mở cho paper E3:**
1. Kiểm trên benchmark ngoài: CityFlow chính chủ hoặc một mạng khác.
2. Hình P5.
3. Bản thảo khớp các câu chữ trên.
4. Thử NI theo từng agent có biên chốt trước, trên panel mới, nếu muốn claim bảo vệ cá thể.
