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

/-- The request heap (`emalloc` arena). The next request reuses the same memory. -/
structure RequestHeap where
  bytes : List UInt8

/-- `zend_string *` stored in `PS(id)`. -/
structure SessionId where
  off : Nat
  len : Nat

/-- Process-lifetime globals of one PHP worker. `psId` is `PS(id)`. -/
structure Worker where
  psId : Option SessionId

/-- End of a request: every allocation dies. -/
def RequestHeap.destroy (_h : RequestHeap) : RequestHeap :=
  { bytes := [] }

/-- `emalloc` in the next request: the attacker's request body reclaims the memory. -/
def RequestHeap.alloc (h : RequestHeap) (b : UInt8) : RequestHeap :=
  { bytes := h.bytes ++ [b] }

/-- `MULTIPART_EVENT_FILE_START`: allocate the id on the request heap and publish it. -/
def publishSessionId (_w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  ({ psId := some ⟨h.bytes.length, 1⟩ }, h.alloc sid)

/-- `php_rshutdown_session_globals`. -/
def rshutdownSessionGlobals (_w : Worker) : Worker :=
  { psId := none }

/-- `MULTIPART_EVENT_END`: clear the globals, then the heap dies. -/
def requestEndNormal (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- THE BUG, unchanged: `zend_bailout` skips `php_rshutdown_session_globals`. -/
def requestEndFatalOom (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (w, h.destroy)

/-- The same fatal edge with the fix. -/
def requestEndFatalOomFixed (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- The next request, as PHP does it: trust `PS(id)`'s pointer and length. `List.drop` and
`List.take` are total, so there is no bounds obligation to fail. -/
def uploadProgressCleanup (w : Worker) (h : RequestHeap) : List UInt8 :=
  match w.psId with
  | some id => (h.bytes.drop id.off).take id.len
  | none => []

theorem destroy_spec (h : RequestHeap) : h.destroy.bytes = [] := rfl

theorem alloc_spec (h : RequestHeap) (b : UInt8) : (h.alloc b).bytes = h.bytes ++ [b] := rfl

theorem publishSessionId_spec (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (publishSessionId w h sid).1.psId = some ⟨h.bytes.length, 1⟩ ∧
    (publishSessionId w h sid).2.bytes = h.bytes ++ [sid] := ⟨rfl, rfl⟩

theorem rshutdownSessionGlobals_spec (w : Worker) : (rshutdownSessionGlobals w).psId = none := rfl

theorem requestEndNormal_frees_heap (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (requestEndNormal w h sid).2.bytes = [] := rfl

/-- The bug edge. Its own spec, "the request heap is gone", is true, so it is proved. -/
theorem requestEndFatalOom_frees_heap (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (requestEndFatalOom w h sid).2.bytes = [] := rfl

theorem requestEndFatalOomFixed_frees_heap (w : Worker) (h : RequestHeap) (sid : UInt8) :
    (requestEndFatalOomFixed w h sid).2.bytes = [] := rfl

/-- Memory safety of the read: the cookie never extends past the heap. -/
theorem uploadProgressCleanup_within_heap (w : Worker) (h : RequestHeap) :
    (uploadProgressCleanup w h).length ≤ h.bytes.length := by
  unfold uploadProgressCleanup
  split <;> simp
  omega

/-- A test, not a spec: request 1 dies of OOM, request 2 reclaims the memory, and the cookie of
request 2 is made of whatever sits where request 1's session id was. -/
theorem test_fatal_oom_leaks_reclaimed_bytes :
    let (w, h) := requestEndFatalOom ⟨none⟩ ⟨[]⟩ 83   -- 'S', request 1's session id
    uploadProgressCleanup w (h.alloc 88) = [88] := by  -- 'X', someone else's bytes
  decide

theorem test_fixed_edge_leaks_nothing :
    let (w, h) := requestEndFatalOomFixed ⟨none⟩ ⟨[]⟩ 83
    uploadProgressCleanup w (h.alloc 88) = [] := by
  decide

end Php2Shell
