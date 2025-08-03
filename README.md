Bidirectional type inference

First pass does linearisation which allows separating walking the AST tree from the type inference.

The second pass does type inference and because it is linearised it is able to pause/resume. This is useful to concurrently type check other functions/modules on the fly when external types are neded, also for compiling compile time meta-programming code that is dependent on types.

```bash
FORCE_COLOR=1 bun test &> out.txt
```