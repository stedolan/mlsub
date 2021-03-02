(rule
 (target t.out)
 (deps (:run ../test_runner.exe) (:in t))
 (action (with-stdout-to %{target} (with-stdin-from %{in} (run %{run})))))
(rule
 (alias runtest)
 (action (diff t t.out)))