/-!
PHP2Shell, session upload-progress (CVE-2026-109618), smallest model, in Lean 4.

This project does NOT chase the bug. It is the same feature as `php2shell-lean-chase`,
ported line for line from PHP, with no property written about the bug. Each function gets the
theorem a careful port would give it: what that one function does. No theorem says anything
that spans two requests.

The PHP feature, and only it:
1. `MULTIPART_EVENT_FILE_START`: during multipart parse, before normal request init, the
   session id is allocated on the request heap and published in the worker global `PS(id)`.
2. Normal end: `php_rshutdown_session_globals` clears `PS(id)`, then the heap is destroyed.
3. Fatal out-of-memory: `zend_bailout` (a longjmp) skips step 2's clear; the heap is destroyed
   anyway, and `PS(id)` keeps pointing into it.
4. The next request on the same worker reaches upload-progress cleanup, trusts `PS(id)`
   (pointer + length) and copies those bytes into the `PHPSESSID` cookie.
-/

namespace Php2Shell

/-- The request heap: PHP's per-request `emalloc` arena. The next request reuses the same
memory, which is what turns a stale pointer into a leak. No generation: as in C, nothing
records which request a byte belongs to. -/
structure RequestHeap where
  bytes : List UInt8

/-- The value of `PS(id)`: in PHP a `zend_string *`, here an offset and a length into the heap. -/
structure SessionId where
  off : Nat
  len : Nat

/-- One PHP worker process. It serves many requests in turn and its globals outlive all of them.
`psId` stands for `PS(id)`, the session module's current session id. -/
structure Worker where
  psId : Option SessionId

/-- End of a request (`shutdown_memory_manager` in PHP): every allocation dies. -/
def RequestHeap.destroy (_h : RequestHeap) : RequestHeap :=
  { bytes := [] }

/-- An `emalloc` in the next request. In the attack, the attacker's request body lands in the
freed slot. -/
def RequestHeap.alloc (h : RequestHeap) (b : UInt8) : RequestHeap :=
  { bytes := h.bytes ++ [b] }

/-- PHP: the session upload-progress handler (`ext/session/session.c`, RFC 1867 callback) on
`MULTIPART_EVENT_FILE_START`. It allocates the session id on the request heap and stores
it in `PS(id)`. -/
def publishSessionId (_w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  ({ psId := some ⟨h.bytes.length, 1⟩ }, h.alloc sid)

/-- PHP: `php_rshutdown_session_globals`, which clears `PS(id)`. The call the bug skips. -/
def rshutdownSessionGlobals (_w : Worker) : Worker :=
  { psId := none }

/-- PHP: `MULTIPART_EVENT_END`, the normal end: clear `PS(id)`, then free the heap. -/
def requestEndNormal (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- THE BUG (CVE-2026-109618), unchanged from `php2shell-lean-chase`: out of memory,
`zend_bailout` skips `php_rshutdown_session_globals`, the heap is freed, `PS(id)` dangles. -/
def requestEndFatalOom (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (w, h.destroy)

/-- The same edge with the fix: clear the globals before freeing the heap. -/
def requestEndFatalOomFixed (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- PHP: the next request's upload-progress cleanup trusts `PS(id)` and copies those bytes into
the `PHPSESSID` cookie. `List.drop`/`List.take` are total, so unlike the Verus port
there is no bounds obligation that could fail. Lean gives no warning at all here. -/
def uploadProgressCleanup (w : Worker) (h : RequestHeap) : List UInt8 :=
  match w.psId with
  | some id => (h.bytes.drop id.off).take id.len
  | none => []

/-- Spec of `destroy`: the heap is empty. Proved. -/
theorem destroy_spec (h : RequestHeap) : h.destroy.bytes = [] := rfl

/-- Spec of `alloc`: one byte appended. Proved. -/
theorem alloc_spec (h : RequestHeap) (b : UInt8) : (h.alloc b).bytes = h.bytes ++ [b] := rfl

/-- Spec of `publishSessionId`: `PS(id)` points at the new byte. Proved. -/
theorem publishSessionId_spec (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (publishSessionId w h sid).1.psId = some ⟨h.bytes.length, 1⟩ ∧
    (publishSessionId w h sid).2.bytes = h.bytes ++ [sid] := ⟨rfl, rfl⟩

/-- Spec of `rshutdownSessionGlobals`: `PS(id)` is cleared. Proved. -/
theorem rshutdownSessionGlobals_spec (w : Worker) : (rshutdownSessionGlobals w).psId = none := rfl

/-- The normal end frees the heap. Proved. -/
theorem requestEndNormal_frees_heap (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (requestEndNormal w h sid).2.bytes = [] := rfl

/-- THE BUG EDGE, with the spec a careful port gives it: "the request heap is freed". True,
so proved. No theorem relates `PS(id)` to the heap, so nothing on this edge can fail. The
vulnerable code is fully verified: this is the finding of this repo. -/
theorem requestEndFatalOom_frees_heap (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (requestEndFatalOom w h sid).2.bytes = [] := rfl

/-- The fixed edge frees the heap. Proved, with the same statement as the bug edge: the specs
cannot tell the bug and the fix apart. -/
theorem requestEndFatalOomFixed_frees_heap (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (requestEndFatalOomFixed w h sid).2.bytes = [] := rfl

/-- Memory safety of the read: the cookie is never longer than the heap. Proved. Safe and still
wrong: it can be another request's bytes. -/
theorem uploadProgressCleanup_within_heap (w : Worker) (h : RequestHeap) :
    (uploadProgressCleanup w h).length ≤ h.bytes.length := by
  unfold uploadProgressCleanup
  split <;> simp
  omega

/-- A test, not a spec: request 1 dies of OOM after publishing 'S' (83), request 2 allocates
'X' (88) in the same slot, and request 2's cookie is [88]. Proved by `decide`. It shows the
leak only because someone wrote this exact sequence. -/
theorem test_fatal_oom_leaks_reclaimed_bytes :
    let (w, h) := requestEndFatalOom ⟨none⟩ ⟨[]⟩ 83   -- 'S', request 1's session id
    uploadProgressCleanup w (h.alloc 88) = [88] := by  -- 'X', someone else's bytes
  decide

/-- The same sequence after the fixed edge: the cookie is empty. Proved by `decide`. -/
theorem test_fixed_edge_leaks_nothing :
    let (w, h) := requestEndFatalOomFixed ⟨none⟩ ⟨[]⟩ 83
    uploadProgressCleanup w (h.alloc 88) = [] := by
  decide

end Php2Shell
