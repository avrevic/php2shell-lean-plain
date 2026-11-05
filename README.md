# php2shell-lean-plain

The smallest model of one [PHP2Shell](https://www.wiz.io/blog/php2shell-php-rce) bug (CVE-2026-109618, session upload-progress memory disclosure), in Lean 4. This version **does not chase the bug**. Each function has the theorem a careful port would give it, which says what that one function does. No theorem spans two requests.

Same model with the property that catches the bug: [php2shell-lean-chase](https://github.com/avrevic/php2shell-lean-chase). Verus versions: [php2shell-chase](https://github.com/avrevic/php2shell-chase), [php2shell-plain](https://github.com/avrevic/php2shell-plain).

| Theorem | Status |
|---|---|
| `destroy_spec`, `alloc_spec`, `publishSessionId_spec`, `rshutdownSessionGlobals_spec` | proved |
| `requestEndNormal_frees_heap` | proved |
| `requestEndFatalOom_frees_heap` (**the bug**) | **proved** |
| `requestEndFatalOomFixed_frees_heap` | proved |
| `uploadProgressCleanup_within_heap` (memory safety of the read) | proved |
| `test_fatal_oom_leaks_reclaimed_bytes` (a test, not a spec) | proved: the cookie holds another request's byte |

Every theorem is proved. Nothing is unverified. In Lean the read is `List.drop`/`List.take`, which is total, so there is no bounds obligation to fail, unlike in Verus. The leak shows up only in the concrete test, which someone has to think of writing. **Without a property that spans requests, verification does not find the flaw.**

```sh
lake build
probe-lean extract .       # VeriLib probe output in .verilib/probes/
```
