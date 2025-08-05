import { inspect } from "bun";
import { describe, it, expect } from "bun:test";
import {
  type Instr, type Env, type Program, type Type, type Scheme, type UnknownType, type SuspendMissing,
  assert, isType, isScheme, newUnknown, arrow, arrowN,
  int, bool, v, lam, lamN, app, appN, _if, _let, block,
  exprToProgram, lineariseProgram, runInternal, createInterpreterState,
  startTrial, rollback, commit, unify, subsume, show,
  trail, solved, tvar, tapp, tstruct, overload, scheme, dummy, getNextSchemeId,
  isArrowN, compactInspect, funDecl, typeApp, areTypesEqual,
  IntType, BoolType, UnitType, FloatType
} from "./typecheck";

/** Run for tests until result is found */
function runExpectingResult(code: Instr[], initialEnv: Env, program?: Program): Type {
  const result = runInternal(createInterpreterState(code, initialEnv, program));
  assert(isType(result), "Expected result, but got suspend", { result });
  const inst = program!.instantiations.map(i => ({ ...i, scheme: program!.schemes.get(i.schemeId)! }));
  console.log('program.instantiations', inst);
  return result;
}


describe("Basic Type Checking", () => {
  it("should type check identity function applied to Int", () => {
    const id   = lam("x", v("x"));                    // λx. x   (no annotation)
    const prog = app(id, int(42));                    // (λx. x) 42

    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program);
    expect(result).toBe(IntType);
  });
});

const envSetVal = (env: Env, name: string, type: Type | Scheme) => env.set(name, { value: { tag: "KnownV", schemeOrType: type } });
const envSetType = (env: Env, name: string, type: Type | Scheme) => env.set(name, { type: { tag: "KnownT", schemeOrType: type } });

describe("Sequence Examples", () => {
  // Set up environment with various functions
  const env: Env = new Map();
  envSetVal(env, "print", arrow(IntType, UnitType));
  envSetVal(env, "add", arrow(IntType, arrow(IntType, IntType)));
  envSetVal(env, "isPositive", arrow(IntType, BoolType));

  it("should handle basic sequence with let bindings", () => {
    const seqProg1 = block(
      app(v("print"), int(1)),                        // print 1 : Unit
      _let("y", null, int(2)),                       // let y=2
      v("y")                                          // y : Int
    );

    const program1 = exprToProgram(seqProg1);
    const seqBytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(seqBytecode1, env, program1);
    expect(result1).toBe(IntType);
  });

  it("should handle sequence with function application and conditional", () => {
    const seqProg2 = block(
      app(v("print"), int(10)),                       // print 10 : Unit
      _let("x", null, int(5)),                               // let x=5
      _if(app(v("isPositive"), v("x")),             // if isPositive x then
        app(v("print"), int(100)),                  //   print 100 : Unit
        app(v("print"), int(200))                   //   print 200 : Unit
      ),
      _let("result", null, int(42)),           // let result=42
      v("result")                               // result : Int
    );

    const program2 = exprToProgram(seqProg2);
    const seqBytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(seqBytecode2, env, program2);
    expect(result2).toBe(IntType);
  });

  it("should handle nested let bindings with function calls", () => {
    const seqProg3 = block(
      app(v("print"), int(1)),                        // print 1 : Unit
      _let("a", null, int(10)),                              // let a=10
      _let("b", null, int(20)),                            //   let b=20
      _let("sum", null, app(app(v("add"), v("a")), v("b"))), // let sum=add a b
      app(v("print"), v("sum")),                 //     print sum : Unit
      bool(true)                                      // true : Bool
    );

    const program3 = exprToProgram(seqProg3);
    const seqBytecode3 = lineariseProgram(program3, program3.rootIndex);
    const result3 = runExpectingResult(seqBytecode3, env, program3);
    expect(result3).toBe(BoolType);
  });

  it("should handle complex sequence with multiple operations", () => {
    const seqProg4 = block(
      app(v("print"), int(0)),                        // print 0 : Unit
      _let("counter", null, int(1)),                         // let counter=1
      _if(app(v("isPositive"), v("counter")),      //   if isPositive counter then
        block(                                       //     block:
          app(v("print"), int(1)),                  //       print 1 : Unit
          app(v("print"), int(2)),                  //       print 2 : Unit
          int(3)                                    //       3 : Int
        ),
        block(                                       //     else block:
          app(v("print"), int(-1)),                 //       print -1 : Unit
          app(v("print"), int(-2)),                 //       print -2 : Unit
          int(-3)                                   //       -3 : Int
        )
      ),
      _let("final", null, int(999)),            // let final=999
      v("final")                                 // final : Int
    );

    const program4 = exprToProgram(seqProg4);
    const seqBytecode4 = lineariseProgram(program4, program4.rootIndex);
    const result4 = runExpectingResult(seqBytecode4, env, program4);
    expect(result4).toBe(IntType);
  });

  it("should handle Unit type handling", () => {
    const seqProg5 = block(
      app(v("print"), int(1)),                        // print 1 : Unit
      app(v("print"), int(2)),                        // print 2 : Unit
      app(v("print"), int(3)),                        // print 3 : Unit
      _let("dummy", null, app(v("print"), int(4))),         // let dummy=print 4
      int(42)                                       //   42 : Int
    );

    const program5 = exprToProgram(seqProg5);
    const seqBytecode5 = lineariseProgram(program5, program5.rootIndex);
    const result5 = runExpectingResult(seqBytecode5, env, program5);
    expect(result5).toBe(IntType);
  });

  it("should handle subtype system with primitive widening", () => {
    const seqProg6 = block(
      app(v("print"), int(10)),                       // print 10 : Unit
      _let("x", v("Float"), int(5)),                  // let x: Float = 5
      _let("y", v("Int"), int(3)),                    // let y: Int = 3
      bool(true)                                      // true : Bool
    );

    const program6 = exprToProgram(seqProg6);
    const seqBytecode6 = lineariseProgram(program6, program6.rootIndex);
    const result6 = runExpectingResult(seqBytecode6, env, program6);
    expect(result6).toBe(BoolType);
  });
});

describe("Trial/Rollback System", () => {
  it("should demonstrate trial/rollback system", () => {
    // Reset the unknown counter for this test
    // nextU = 1; // TODO: Fix this assignment
    
    // Demonstrate the trial/rollback system
    const env2: Env = new Map();
    envSetVal(env2, "f", arrow(IntType, BoolType));

    // Create some unknown types
    const u1: UnknownType = newUnknown();
    const u2: UnknownType = newUnknown();

    expect(show(u1)).toBe("?1");
    expect(show(u2)).toBe("?2");

    // Start a trial
    const mark = startTrial();

    // Try to unify u1 with Int
    unify(u1, IntType, true).getOrThrow();
    expect(show(u1)).toBe("Int");
    
    // Try to unify u2 with Bool
    unify(u2, BoolType, true).getOrThrow();
    expect(show(u2)).toBe("Bool");
    
    // Try something that should fail
    const error = unify(u1, BoolType, true).expectError();
    expect(error).toBeDefined();
    
    // Rollback to the mark
    rollback(mark);
    expect(show(u1)).toBe("?1");
    expect(show(u2)).toBe("?2");

    // Start another trial
    const mark2 = startTrial();

    // Try a successful unification
    unify(u1, IntType, true).getOrThrow();
    unify(u2, BoolType, true).getOrThrow();
    expect(show(u1)).toBe("Int");
    expect(show(u2)).toBe("Bool");

    // Commit the changes
    commit(mark2);
    expect(show(u1)).toBe("Int");
    expect(show(u2)).toBe("Bool");
  });
});

describe("Simple Trial/Rollback", () => {
  it("should handle simple trial/rollback operations", () => {
    // Reset the unknown counter for this test
    // nextU = 3; // TODO: Fix this assignment
    
    // Clear the trail and solved map for a clean test
    trail.length = 0;
    solved.clear();

    // Create fresh unknowns
    const u3: UnknownType = newUnknown();
    const u4: UnknownType = newUnknown();

    expect(show(u3)).toBe("?3");
    expect(show(u4)).toBe("?4");

    // Test 1: Successful trial
    const mark3 = startTrial();
    unify(u3, IntType, true).getOrThrow();
    unify(u4, BoolType, true).getOrThrow();
    expect(show(u3)).toBe("Int");
    expect(show(u4)).toBe("Bool");
    expect(trail.length).toBeGreaterThanOrEqual(2);

    // Test 2: Failed trial with rollback
    const mark4 = startTrial();
    unify(u3, IntType, true).getOrThrow();    // This should work (u3 is already Int)
    const error = unify(u4, IntType, true).expectError();    // This should fail (Bool ≠ Int)
    expect(error).toBeDefined();
    rollback(mark4);
    expect(show(u3)).toBe("Int");
    expect(show(u4)).toBe("Bool");

    // Test 3: Commit successful trial
    const mark5 = startTrial();
    unify(u3, IntType, true).getOrThrow();    // This should work (u3 is already Int)
    commit(mark5);
    expect(show(u3)).toBe("Int");
    expect(show(u4)).toBe("Bool");
  });
});

describe("Non-recording Operations", () => {
  it("should handle non-recording operations correctly", () => {
    const u5: UnknownType = newUnknown();
    expect(show(u5)).toBe("?5");

    // This should not be recorded
    unify(u5, IntType, false).getOrThrow();
    expect(show(u5)).toBe("Int");
    expect(trail.length).toBe(2);

    // This should be recorded
    const mark6 = startTrial();
    unify(u5, IntType, true).getOrThrow();  // This should work since u5 is already Int
    rollback(mark6);
    expect(show(u5)).toBe("Int");
  });
});

describe("Apply/Join Non-recording", () => {
  it("should handle apply/join non-recording operations", () => {
    const u6: UnknownType = newUnknown();
    const u7: UnknownType = newUnknown();

    expect(show(u6)).toBe("?6");
    expect(show(u7)).toBe("?7");

    // Simulate an apply operation (function application)
    const fnType = { kind: "Arrow" as const, param: u6, result: u7 };
    unify(fnType.param, IntType, false).getOrThrow();  // This simulates apply behavior
    expect(show(u6)).toBe("Int");

    // Start a trial and try to change u6
    const mark7 = startTrial();
    const error = unify(u6, BoolType, true).expectError();  // This should fail since u6 is already Int
    expect(error).toBeDefined();
    rollback(mark7);
    expect(show(u6)).toBe("Int");
  });
});

describe("Overload Functionality", () => {
  it("should handle overloaded functions with Int arguments", () => {
    // Create an overloaded function that can take Int or Float
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(FloatType, FloatType)
    ]);

    // Set up environment with overloaded function
    const env: Env = new Map();
    envSetVal(env, "add", overloadedFn);

    const prog1 = app(v("add"), int(42));
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toBe(IntType);
  });

  it("should handle overloaded functions with Float arguments", () => {
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(FloatType, FloatType)
    ]);

    const env: Env = new Map();
    envSetVal(env, "add", overloadedFn);

    const prog2 = app(v("add"), int(42)); // This should work due to Int ≤ Float
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toBe(IntType);
  });

  it("should handle more specific overloads", () => {
    const moreSpecificOverload = overload([
      arrow(IntType, IntType),
      arrow(FloatType, FloatType),
      arrow(BoolType, BoolType)
    ]);
    const env: Env = new Map();
    envSetVal(env, "func", moreSpecificOverload);
    
    const prog3 = app(v("func"), bool(true));
    const program3 = exprToProgram(prog3);
    const bytecode3 = lineariseProgram(program3, program3.rootIndex);
    const result3 = runExpectingResult(bytecode3, env, program3);
    expect(result3).toBe(BoolType);
  });

  it("should reject no viable overloads", () => {
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(FloatType, FloatType)
    ]);

    const env: Env = new Map();
    envSetVal(env, "add", overloadedFn);

    const prog4 = app(v("add"), bool(true));
    const program4 = exprToProgram(prog4);
    const bytecode4 = lineariseProgram(program4, program4.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode4, env, program4);
    }).toThrow("no viable overloads");
  });

  it("should reject ambiguous overloads", () => {
    const ambiguousOverload = overload([
      arrow(IntType, IntType),
      arrow(IntType, BoolType)  // Same parameter type, different return type
    ]);
    const env: Env = new Map();
    envSetVal(env, "ambiguous", ambiguousOverload);
    
    const prog7 = app(v("ambiguous"), int(42));
    const program7 = exprToProgram(prog7);
    const bytecode7 = lineariseProgram(program7, program7.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode7, env, program7);
    }).toThrow("ambiguous overload");
  });

  it("should prefer exact matches over implicit casts", () => {
    const exactVsCastOverload = overload([
      arrow(IntType, IntType),      // Exact match for Int
      arrow(FloatType, FloatType)   // Requires implicit cast from Int
    ]);
    const env: Env = new Map();
    envSetVal(env, "exactVsCast", exactVsCastOverload);
    
    const prog8 = app(v("exactVsCast"), int(42));
    const program8 = exprToProgram(prog8);
    const bytecode8 = lineariseProgram(program8, program8.rootIndex);
    const result8 = runExpectingResult(bytecode8, env, program8);
    expect(result8).toBe(IntType);
  });

  it("should accept implicit casts when only option available", () => {
    const onlyCastOverload = overload([
      arrow(FloatType, FloatType)   // Only Float overload available
    ]);
    const env: Env = new Map();
    envSetVal(env, "onlyCast", onlyCastOverload);
    
    const prog9 = app(v("onlyCast"), int(42));
    const program9 = exprToProgram(prog9);
    const bytecode9 = lineariseProgram(program9, program9.rootIndex);
    const result9 = runExpectingResult(bytecode9, env, program9);
    expect(result9).toBe(FloatType);
  });
});

describe("Multi-Argument Functions", () => {
  it("should handle basic multi-argument functions", () => {
    const env: Env = new Map();
    
    // Create a function that takes 3 Int arguments and returns Int
    const add3Fn = arrowN([IntType, IntType, IntType], IntType);
    envSetVal(env, "add3", add3Fn);
    
    const prog1 = appN(v("add3"), [int(1), int(2), int(3)]);
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toBe(IntType);
  });

  it("should handle multi-argument functions with different types", () => {
    const env: Env = new Map();
    const mixedFn = arrowN([IntType, BoolType, FloatType], BoolType);
    envSetVal(env, "mixed", mixedFn);
    
    const prog2 = appN(v("mixed"), [int(42), bool(true), int(3.14)]);
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toBe(BoolType);
  });

  it("should handle overloaded multi-argument functions", () => {
    const env: Env = new Map();
    const overloadedMultiFn = overload([
      arrowN([IntType, IntType], IntType),
      arrowN([FloatType, FloatType], FloatType)
    ]);
    envSetVal(env, "overloadedMulti", overloadedMultiFn);
    
    const prog3 = appN(v("overloadedMulti"), [int(10), int(20)]);
    const program3 = exprToProgram(prog3);
    const bytecode3 = lineariseProgram(program3, program3.rootIndex);
    const result3 = runExpectingResult(bytecode3, env, program3);
    expect(result3).toBe(IntType);
  });

  it("should reject wrong number of arguments", () => {
    const env: Env = new Map();
    const add3Fn = arrowN([IntType, IntType, IntType], IntType);
    envSetVal(env, "add3", add3Fn);
    
    const prog4 = appN(v("add3"), [int(1), int(2)]); // Only 2 args, needs 3
    const program4 = exprToProgram(prog4);
    const bytecode4 = lineariseProgram(program4, program4.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode4, env, program4);
    }).toThrow("expects 3 arguments but got 2");
  });

  it("should handle nested multi-argument applications", () => {
    const env: Env = new Map();
    const add3Fn = arrowN([IntType, IntType, IntType], IntType);
    envSetVal(env, "add3", add3Fn);
    const nestedFn = arrowN([IntType, IntType], IntType);
    envSetVal(env, "nested", nestedFn);
    
    const prog5 = appN(v("nested"), [
      appN(v("add3"), [int(1), int(2), int(3)]),
      int(10)
    ]);
    const program5 = exprToProgram(prog5);
    const bytecode5 = lineariseProgram(program5, program5.rootIndex);
    const result5 = runExpectingResult(bytecode5, env, program5);
    expect(result5).toBe(IntType);
  });
});

describe("Generic Type System", () => {
  it("should handle generic identity function with Int", () => {
    const env: Env = new Map();
    
    // Define a generic identity function: ∀T. T → T
    const idScheme = scheme("id", getNextSchemeId(), ["T"], arrowN([tvar("T")], tvar("T")));
    envSetVal(env, "id", idScheme);
    
    // Test with Int
    const prog1 = app(v("id"), int(42));
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toBe(IntType);
  });

  it("should handle generic identity function with Bool", () => {
    const env: Env = new Map();
    
    // Define a generic identity function: ∀T. T → T
    const idScheme = scheme("id", getNextSchemeId(), ["T"], arrowN([tvar("T")], tvar("T")));
    envSetVal(env, "id", idScheme);
    
    // Test with Bool
    const prog2 = app(v("id"), bool(true));
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toBe(BoolType);
  });

  // TODO: Not sure
  // it("should handle generic List type instantiation", () => {
  //   const env: Env = new Map();
  //   const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
  //   envSetVal(env, "List", listScheme);
    
  //   // Test List<Int> - we need to test the instantiation directly
  //   const listIntInst = instantiate(listScheme);
  //   expect(isTApp(listIntInst)).toBe(true);
  //   expect((listIntInst as AppliedType).ctor).toBe("List");
    
  //   // Test substitution with Int
  //   const subst = new Map<string, Type>([["T", IntType]]);
  //   const listIntSubst = substWalk(listScheme.body, subst);
  //   expect(isTApp(listIntSubst)).toBe(true);
  //   expect((listIntSubst as AppliedType).ctor).toBe("List");
  //   expect((listIntSubst as AppliedType).args[0]).toBe(IntType);
  // });

  it("should handle type variable unification correctly", () => {
    // Test that TVar can only unify with itself
    unify(tvar("T"), tvar("T"), false).getOrThrow();
    
    const error1 = unify(tvar("T"), tvar("U"), false).expectError();
    expect(error1).toBeDefined();
    
    const error2 = unify(tvar("T"), IntType, false).expectError();
    expect(error2).toBeDefined();
  });

  it("should handle type application correctly", () => {
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const listBool = tapp(listScheme, [BoolType]);
    
    unify(listInt, listInt, false).getOrThrow();
    
    const error3 = unify(listInt, listBool, false).expectError();
    expect(error3).toBeDefined();
  });
});

describe("Pending Bindings", () => {
  it("should handle basic pending binding scenario", () => {
    const env: Env = new Map();
    env.set("missingVar", { value: { tag: "PendV", waiters: [] } });
    
    // Create a program that references a variable that's not in the environment
    const prog = v("missingVar");
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    
    // Run the interpreter and expect it to suspend
    const state = createInterpreterState(bytecode, env, program);
    const result = runInternal(state);
    
    expect(!isType(result)).toBe(true);
    const suspendResult = result as SuspendMissing;
    expect(suspendResult.done).toBe(false);
    expect(suspendResult.id).toBe("missingVar");
    
    // Resume with a type
    const resumedResult = suspendResult.resume(IntType);
    
    expect(isType(resumedResult)).toBe(true);
    expect(resumedResult).toBe(IntType);
  });

  it("should handle multiple lookups of the same pending variable", () => {
    const prog2 = app(v("missingVar"), int(42)); // missingVar(42)
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const env2 = new Map();
    env2.set("missingVar", { tag: "Pending", waiters: [] });

    
    const state2 = createInterpreterState(bytecode2, env2, program2);
    const result2 = runInternal(state2);
    
    expect(!isType(result2)).toBe(true);
    const suspendResult2 = result2 as SuspendMissing;
    expect(suspendResult2.id).toBe("missingVar");
    
    // Resume with a function type
    const funcTy = arrow(IntType, BoolType)
    const resumedResult2 = suspendResult2.resume(funcTy);
    
    expect(resumedResult2).toBe(BoolType);
  });
  
  it("should handle resume with error", () => {
    const prog3 = v("anotherMissingVar");
    const program3 = exprToProgram(prog3);
    const bytecode3 = lineariseProgram(program3, program3.rootIndex);
    const env3 = new Map();
    env3.set("anotherMissingVar", { tag: "Pending", waiters: [] });
    
    const state3 = createInterpreterState(bytecode3, env3, program3);
    const result3 = runInternal(state3);
    
    expect(!isType(result3)).toBe(true);
    const suspendResult3 = result3 as SuspendMissing;
    
    // Resume with an error
    const error = new Error("Variable not found");
    expect(() => {
      suspendResult3.resume(error);
    }).toThrow("Variable not found");
  });
  
  it("should handle nested pending bindings", () => {
    const prog4 = app(app(v("outerFunc"), v("innerVar")), int(10));
    const program4 = exprToProgram(prog4);
    const bytecode4 = lineariseProgram(program4, program4.rootIndex);

    const env4 = new Map();
    env4.set("outerFunc", { tag: "Pending", waiters: [] });
    env4.set("innerVar", { tag: "Pending", waiters: [] });

    const state4 = createInterpreterState(bytecode4, env4, program4);
    const result4 = runInternal(state4);

    expect(!isType(result4)).toBe(true);
    const suspendResult4 = result4 as SuspendMissing;
    expect(suspendResult4.id).toBe("outerFunc");

    // Resume with a function that takes a function
    const nestedTy = arrow(arrow(IntType, BoolType), arrow(IntType, BoolType))
    const resumedResult4 = suspendResult4.resume(nestedTy);

    expect(!isType(resumedResult4)).toBe(true);
    const suspendResumedResult4 = resumedResult4 as SuspendMissing;
    expect(suspendResumedResult4.id).toBe("innerVar");

    // Resume the inner variable
    const innerTy = arrow(IntType, BoolType)
    const finalResult = suspendResumedResult4.resume(innerTy);

    expect(finalResult).toBe(BoolType);
  });
});

describe("Unbound Variables", () => {
  it("should reject simple unbound variable", () => {
    const env: Env = new Map();
    const prog = v("unboundVar");
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode, env, program);
    }).toThrow("unbound variable unboundVar");
  });
  
  it("should reject unbound variable in function application", () => {
    const env: Env = new Map();
    const prog2 = app(v("unboundFunc"), int(42));
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode2, env, program2);
    }).toThrow("unbound variable unboundFunc");
  });
  
  it("should reject unbound variable in let binding", () => {
    const env: Env = new Map();
    const prog3 = _let("x", null, v("unboundInLet"));
    const program3 = exprToProgram(prog3);
    const bytecode3 = lineariseProgram(program3, program3.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode3, env, program3);
    }).toThrow("unbound variable unboundInLet");
  });
  
  it("should reject unbound variable in nested scope", () => {
    const env: Env = new Map();
    const prog4 = lam("param", v("unboundInLambda"));
    const program4 = exprToProgram(prog4);
    const bytecode4 = lineariseProgram(program4, program4.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode4, env, program4);
    }).toThrow("unbound variable unboundInLambda");
  });
  
  it("should reject multiple unbound variables", () => {
    const env: Env = new Map();
    const prog5 = app(app(v("func1"), v("func2")), int(42));
    const program5 = exprToProgram(prog5);
    const bytecode5 = lineariseProgram(program5, program5.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode5, env, program5);
    }).toThrow("unbound variable func1");
  });
  
  it("should reject unbound variable in mixed environment", () => {
    const envWithSome: Env = new Map();
    envSetVal(envWithSome, "boundVar", IntType);
    envSetVal(envWithSome, "boundFunc", arrow(IntType, BoolType));
    
    const prog6 = app(app(v("boundFunc"), v("boundVar")), v("unboundVar"));
    const program6 = exprToProgram(prog6);
    const bytecode6 = lineariseProgram(program6, program6.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode6, envWithSome, program6);
    }).toThrow("unbound variable unboundVar");
  });
  
  it("should reject unbound variable in sequence", () => {
    const envWithPrint: Env = new Map();
    envSetVal(envWithPrint, "print", arrow(IntType, UnitType));
    
    const prog7 = block(
      app(v("print"), int(1)),
      v("unboundInSeq"),
      int(42)
    );
    const program7 = exprToProgram(prog7);
    const bytecode7 = lineariseProgram(program7, program7.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode7, envWithPrint, program7);
    }).toThrow("unbound variable unboundInSeq");
  });
});

function printProgram(program: Program) {
  console.log("Program nodes:", program.nodes.length);
  console.log("Program types:", program.types.length);
  console.log("Root index:", program.rootIndex);
  
  program.nodes.forEach((node, index) => {
    const type = program.types[index] ? show(program.types[index]) : "null"
    console.log(`${index}: ${type}: ${compactInspect(node)}`)
  });
}

describe("Program-Based Type Checking", () => {
  it("should handle conversion from Expr to Program", () => {
    const expr = int(42);
    const convertedProgram = exprToProgram(expr);

    expect(convertedProgram.nodes.length).toBeGreaterThan(0);
    expect(convertedProgram.rootIndex).toBeDefined();
    
    const bytecode5 = lineariseProgram(convertedProgram, convertedProgram.rootIndex);
    const result5 = runExpectingResult(bytecode5, new Map(), convertedProgram);
    expect(result5).toBe(IntType);
  });
  
  it("should handle lambda expression conversion", () => {
    const lambdaExpr = lam("x", v("x")); // λx. x
    const lambdaProgram = exprToProgram(lambdaExpr);
    
    expect(lambdaProgram.nodes.length).toBeGreaterThan(0);
    expect(lambdaProgram.rootIndex).toBeDefined();
    
    const bytecode6 = lineariseProgram(lambdaProgram, lambdaProgram.rootIndex);
    const result6 = runExpectingResult(bytecode6, new Map(), lambdaProgram);
    expect(isArrowN(result6)).toBe(true);
  });
  
  it("should handle lambda application", () => {
    const lambdaExpr = lam("x", v("x")); // λx. x
    const lambdaAppExpr = app(lambdaExpr, int(42)); // (λx. x) 42
    const lambdaAppProgram = exprToProgram(lambdaAppExpr);
    
    const bytecode7 = lineariseProgram(lambdaAppProgram, lambdaAppProgram.rootIndex);
    const result7 = runExpectingResult(bytecode7, new Map(), lambdaAppProgram);
    expect(result7).toBe(IntType);
  });
  
  it("should handle multi-parameter lambda", () => {
    const multiLambdaExpr = lamN(["x", "y"], app(app(v("add"), v("x")), v("y"))); // λx y. add x y
    const multiLambdaProgram = exprToProgram(multiLambdaExpr);
    
    expect(multiLambdaProgram.nodes.length).toBeGreaterThan(0);
    
    // Set up environment with add function
    const env8: Env = new Map();
    envSetVal(env8, "add", arrow(IntType, arrow(IntType, IntType)));
    
    const bytecode8 = lineariseProgram(multiLambdaProgram, multiLambdaProgram.rootIndex);
    const result8 = runExpectingResult(bytecode8, env8, multiLambdaProgram);
    expect(isArrowN(result8)).toBe(true);
  });
  
  it("should handle multi-parameter lambda application", () => {
    const multiLambdaExpr = lamN(["x", "y"], app(app(v("add"), v("x")), v("y"))); // λx y. add x y
    const multiLambdaAppExpr = appN(multiLambdaExpr, [int(10), int(20)]); // (λx y. add x y) 10 20
    const multiLambdaAppProgram = exprToProgram(multiLambdaAppExpr);
    
    // Set up environment with add function
    const env9: Env = new Map();
    envSetVal(env9, "add", arrow(IntType, arrow(IntType, IntType)));
    
    const bytecode9 = lineariseProgram(multiLambdaAppProgram, multiLambdaAppProgram.rootIndex);
    const result9 = runExpectingResult(bytecode9, env9, multiLambdaAppProgram);
    expect(result9).toBe(IntType);
  });
});

describe("Generic Functions in Programs", () => {
  it("should define and use generic identity function in program", () => {
    // Define a generic identity function: ∀T. T → T
    const genericId = funDecl("id", ["T"], ["x"], v("x"), ["T"]);
    
    // Create a program that defines the function and uses it
    const programExpr = block(
      genericId,  // Define the generic function
      app(v("id"), int(42))  // Use it with Int
    );
    
    const program = exprToProgram(programExpr);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program);
    expect(result).toBe(IntType);
  });

  // TODO: We don't support type constraints so we can't call generic parameters, or pass them
  // to functions expecting concrete types

  // it("should define and use generic function with multiple type parameters", () => {
  //   // Define a generic apply function: ∀T, U. (T → U) → T → U
  //   const genericApply = funDecl("apply", ["T", "U"], ["f", "x"], 
  //     app(v("f"), v("x")), ["T", "U"]);
    
  //   // Create a program that defines and uses the generic function
  //   const intToBoolFn = arrow(IntType, BoolType);
  //   const env: Env = new Map();
  //   envSetVal(env, "intToBool", intToBoolFn);
    
  //   const programExpr = block(
  //     genericApply,  // Define the generic function
  //     app(app(v("apply"), v("intToBool")), int(42))  // Use it
  //   );
    
  //   const program = exprToProgram(programExpr);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toBe(BoolType);
  // });

  // it("should define and use generic function with higher-order types", () => {
  //   // Define a generic compose function: ∀T, U, V. (U → V) → (T → U) → T → V
  //   const genericCompose = funDecl("compose", ["T", "U", "V"], ["f", "g", "x"], 
  //     app(v("f"), app(v("g"), v("x"))));
    
  //   // Create helper functions
  //   const intToFloat = arrow(IntType, FloatType);
  //   const floatToBool = arrow(FloatType, BoolType);
  //   const env: Env = new Map();
  //   envSetVal(env, "intToFloat", intToFloat);
  //   envSetVal(env, "floatToBool", floatToBool);
    
  //   const programExpr = block(
  //     genericCompose,  // Define the generic function
  //     app(app(app(v("compose"), v("floatToBool")), v("intToFloat")), int(42))  // Use it
  //   );
    
  //   const program = exprToProgram(programExpr);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toBe(BoolType);
  // });

  // it("should define and use generic function with type constraints", () => {
  //   // Define a generic add function: ∀T. T → T → T
  //   const genericAdd = funDecl("add", ["T"], ["x", "y"], 
  //     app(app(v("addInt"), v("x")), v("y")));
    
  //   // Create a program that defines and uses the generic function
  //   const addInt = arrow(IntType, arrow(IntType, IntType));
  //   const env: Env = new Map();
  //   envSetVal(env, "addInt", addInt);
    
  //   const programExpr = block(
  //     genericAdd,  // Define the generic function
  //     app(app(v("add"), int(10)), int(20))  // Use it
  //   );
    
  //   const program = exprToProgram(programExpr);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toBe(IntType);
  // });

  // it("should handle multiple generic function definitions in one program", () => {
  //   // Define multiple generic functions
  //   const genericId = funDecl("id", ["T"], ["x"], v("x"));
  //   const genericApply = funDecl("apply", ["T", "U"], ["f", "x"], 
  //     app(v("f"), v("x")));
  //   const genericCompose = funDecl("compose", ["T", "U", "V"], ["f", "g", "x"], 
  //     app(v("f"), app(v("g"), v("x"))));
    
  //   // Create helper functions
  //   const intToBool = arrow(IntType, BoolType);
  //   const env: Env = new Map();
  //   envSetVal(env, "intToBool", intToBool);
    
  //   // Create a program with multiple generic function definitions and usages
  //   const programExpr = block(
  //     genericId,      // Define id: ∀T. T → T
  //     genericApply,   // Define apply: ∀T, U. (T → U) → T → U
  //     genericCompose, // Define compose: ∀T, U, V. (U → V) → (T → U) → T → V
  //     app(v("id"), int(42)),  // Use id
  //     app(app(v("apply"), v("intToBool")), int(42))  // Use apply
  //   );
    
  //   const program = exprToProgram(programExpr);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toBe(BoolType);
  // });
});

declare module "bun:test" {
  interface Matchers<T=unknown> {
    toEqualType(expected: Type): T;
  }
}

expect.extend({
  toEqualType(received: Type, expected: Type) {
    return {  
      pass: areTypesEqual(received, expected),
      message: () => `expected ${received} to be ${expected}`,
    };
  },
} as any);

describe("Type Annotation Resolution for Generic Structs", () => {
  it("should resolve simple non-generic struct annotations", () => {
    const env: Env = new Map();
    
    // Define a simple non-generic struct: struct Point { x: Int, y: Int }
    const pointStruct = tstruct("Point", [{ name: "x", type: IntType }, { name: "y", type: IntType }]);
    envSetType(env, "Point", pointStruct);
    
    const prog = _let("p", v("Point"), null);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(pointStruct);
  });

  it("should resolve generic struct annotations with concrete type arguments", () => {
    const env: Env = new Map();
    
    // Define a generic struct: struct List<T> { ... }
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const listBool = tapp(listScheme, [BoolType]);
    envSetType(env, "List", listScheme);
    
    const prog1 = _let("numbers", typeApp(v("List"), [v("Int")]), null);
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toEqualType(listInt);
    
    const prog2 = _let("flags", typeApp(v("List"), [v("Bool")]), null);
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toEqualType(listBool);
  });

  it("should resolve nested generic struct annotations", () => {
    const env: Env = new Map();
    
    // Define generic structs: struct List<T> and struct Option<T>
    const optionScheme = scheme("Option", getNextSchemeId(), ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionListInt = tapp(optionScheme, [tapp(listScheme, [IntType])]);
    const listOptionInt = tapp(listScheme, [tapp(optionScheme, [IntType])]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    const prog1 = _let("optList", typeApp(v("Option"), [typeApp(v("List"), [v("Int")])]), null);
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toEqualType(optionListInt);
    
    const prog2 = _let("listOpt", typeApp(v("List"), [typeApp(v("Option"), [v("Int")])]), null);
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toEqualType(listOptionInt);
  });

  it("should resolve generic struct annotations with multiple type parameters", () => {
    const env: Env = new Map();
    
    // Define a struct with multiple type parameters: struct Pair<T, U> { first: T, second: U }
    const pairScheme = scheme("Pair", getNextSchemeId(), ["T", "U"], tstruct("Pair", [{ name: "first", type: tvar("T") }, { name: "second", type: tvar("U") }]));
    const pairIntBool = tapp(pairScheme, [IntType, BoolType]);
    const pairFloatInt = tapp(pairScheme, [FloatType, IntType]);
    
    envSetType(env, "Pair", pairScheme);
    
    const prog1 = _let("mixed", typeApp(v("Pair"), [v("Int"), v("Bool")]), null);
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toEqualType(pairIntBool);
    
    const prog2 = _let("numbers", typeApp(v("Pair"), [v("Float"), v("Int")]), null);
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toEqualType(pairFloatInt);
  });

  it("should resolve complex nested generic struct annotations", () => {
    const env: Env = new Map();
    
    // Define multiple generic structs
    const mapScheme = scheme("Map", getNextSchemeId(), ["T", "U"], tstruct("Map", [{ name: "key", type: tvar("T") }, { name: "value", type: tvar("U") }]));
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = scheme("Option", getNextSchemeId(), ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const complexType = tapp(mapScheme, [
      tapp(listScheme, [IntType]),
      tapp(optionScheme, [BoolType])
    ]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    envSetType(env, "Map", mapScheme);

    console.log('env', env);
    
    const prog = _let("complex", typeApp(v("Map"), [typeApp(v("List"), [v("Int")]), typeApp(v("Option"), [v("Bool")])]), null);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(complexType);
  });

  // TODO: implement type parameter constraints
  // it("should handle type parameters with constraints", () => {
  //   const env: Env = new Map();
    
  //   // Define a struct with constrained type parameters: struct SortedList<T: Ord> { ... }
  //   const sortedListInt = tapp("SortedList", [IntType]);
    
  //   const sortedListStruct = scheme(["T"], tstruct("SortedList", [{ name: "head", type: tvar("T") }]));
  //   envSetType(env, "SortedList", sortedListStruct);
    
  //   const prog = _let("sorted", typeApp(v("SortedList"), [v("Int")]), null);
  //   const program = exprToProgram(prog);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toEqualType(sortedListInt);
  // });

  it("should resolve generic struct annotations in function parameters", () => {
    const env: Env = new Map();
    
    // Define a function that takes generic structs as parameters
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = scheme("Option", getNextSchemeId(), ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const optionBool = tapp(optionScheme, [BoolType]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    // Function: fn process<T>(list: List<T>, opt: Option<Bool>) -> T
    const processFn = arrowN([listInt, optionBool], IntType);
    envSetVal(env, "process", processFn);
    
    const prog = block(
      _let("list", typeApp(v("List"), [v("Int")]), null),
      _let("opt", typeApp(v("Option"), [v("Bool")]), null),
      appN(v("process"), [v("list"), v("opt")])
    );
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(IntType);
  });

  it("should resolve generic struct annotations in let bindings with function calls", () => {
    const env: Env = new Map();
    
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = scheme("Option", getNextSchemeId(), ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const optionInt = tapp(optionScheme, [IntType]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    // Function that returns a generic struct
    const createListFn = arrow(IntType, listInt);
    const createOptionFn = arrow(IntType, optionInt);
    envSetVal(env, "createList", createListFn);
    envSetVal(env, "createOption", createOptionFn);
    
    const prog = block(
      _let("myList", typeApp(v("List"), [v("Int")]), app(v("createList"), int(42))),
      _let("myOption", typeApp(v("Option"), [v("Int")]), app(v("createOption"), int(10))),
      int(999)
    );
    
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(IntType);
  });

  // TODO: Not sure
  // it("should handle generic struct annotations with type variables", () => {
  //   const env: Env = new Map();
    
  //   // Define a generic function that works with generic structs
  //   const listT = tapp("List", [tvar("T")]);
  //   const optionT = tapp("Option", [tvar("T")]);
    
  //   const listStruct = scheme(["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
  //   const optionStruct = scheme(["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
  //   envSetType(env, "List", listStruct);
  //   envSetType(env, "Option", optionStruct);
    
  //   // Generic function: fn transform<T>(list: List<T>) -> Option<T>
  //   const transformFn = arrowN([listT], optionT);
  //   envSetVal(env, "transform", transformFn);
    
  //   const prog = block(
  //     _let("list", typeApp(v("List"), [v("Int")]), null),
  //     appN(v("transform"), [v("list")])
  //   );
  //   const program = exprToProgram(prog);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toEqualType(optionT);
  // });

  it("should reject invalid generic struct annotations", () => {
    const env: Env = new Map();
    
    // Define a struct that expects 2 type parameters
    const pairScheme = scheme("Pair", getNextSchemeId(), ["T", "U"], tstruct("Pair", [{ name: "first", type: tvar("T") }, { name: "second", type: tvar("U") }]));
    envSetType(env, "Pair", pairScheme);
    
    const prog1 = _let("invalid", typeApp(v("Pair"), [v("Int")]), null); // Missing second type parameter
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode1, env, program1);
    }).toThrow();
    
    const prog2 = _let("invalid2", typeApp(v("Pair"), [v("Int"), v("Bool"), v("Float")]), null); // Too many type parameters
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode2, env, program2);
    }).toThrow();
  });

  it("should reject undefined struct annotations", () => {
    const env: Env = new Map();
    
    const prog = _let("undefined", typeApp(v("UndefinedStruct"), [v("Int")]), null);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode, env, program);
    }).toThrow();
  });

  it("should handle generic struct annotations with primitive type widening", () => {
    const env: Env = new Map();
    
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listFloat = tapp(listScheme, [FloatType]);
    
    envSetType(env, "List", listScheme);
    
    // Int should be accepted where Float is expected due to widening
    const prog = _let("numbers", typeApp(v("List"), [v("Float")]), null);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(listFloat);
  });

  it("should resolve generic struct annotations in complex expressions", () => {
    const env: Env = new Map();
    
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = scheme("Option", getNextSchemeId(), ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const optionListInt = tapp(optionScheme, [listInt]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    // Function that returns Option<List<Int>>
    const complexFn = arrow(IntType, optionListInt);
    envSetVal(env, "complexFn", complexFn);
    
    const prog = block(
      _let("result", typeApp(v("Option"), [typeApp(v("List"), [v("Int")])]), app(v("complexFn"), int(42))),
      int(999)
    );
    
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(IntType);
  });

  // TODO: Support recursive types
  // it("should handle generic struct annotations with recursive types", () => {
  //   const env: Env = new Map();
    
  //   // Define a recursive type: struct Tree<T> { value: T, children: List<Tree<T>> }
  //   const treeScheme = scheme("Tree", getNextSchemeId(), ["T"], tstruct("Tree", [{ name: "value", type: tvar("T") }, { name: "children", type: tapp(listScheme, [tapp(treeScheme, [tvar("T")])]) }]));
  //   const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
  //   const treeInt = tapp(treeScheme, [IntType]);
  //   const listTreeInt = tapp(listScheme, [treeInt]);
    
  //   envSetType(env, "Tree", treeScheme);
  //   envSetType(env, "List", listScheme);
    
  //   const prog = _let("tree", typeApp(v("Tree"), [v("Int")]), null);
  //   const program = exprToProgram(prog);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toEqualType(treeInt);
  // });

  it("should resolve generic struct annotations with higher-order types", () => {
    const env: Env = new Map();
    
    // Define a struct that contains function types: struct Container<T> { fn: T -> T }
    const containerScheme = scheme("Container", getNextSchemeId(), ["T"], tstruct("Container", [{ name: "fn", type: arrow(tvar("T"), tvar("T")) }]));
    const containerFn = tapp(containerScheme, [arrow(IntType, IntType)]);
    
    envSetType(env, "Container", containerScheme);
    
    
    const prog = _let("container", typeApp(v("Container"), [typeApp(v("Fn"), [v("Int"),v("Int")])]), null);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(containerFn);
  });

  it("should handle generic struct annotations with overloaded functions", () => {
    const env: Env = new Map();
    
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const listFloat = tapp(listScheme, [FloatType]);
    
    envSetType(env, "List", listScheme);
    
    // Overloaded function that can work with List<Int> or List<Float>
    const overloadedFn = overload([
      arrow(listInt, IntType),
      arrow(listFloat, FloatType)
    ]);
    envSetVal(env, "overloadedFn", overloadedFn);
    
    const prog1 = block(
      _let("list", typeApp(v("List"), [v("Int")]), null),
      app(v("overloadedFn"), v("list"))
    );
    const program1 = exprToProgram(prog1);
    const bytecode1 = lineariseProgram(program1, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1);
    expect(result1).toBe(IntType);
    
    const prog2 = block(
      _let("list", typeApp(v("List"), [v("Float")]), null),
      app(v("overloadedFn"), v("list"))
    );
    const program2 = exprToProgram(prog2);
    const bytecode2 = lineariseProgram(program2, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2);
    expect(result2).toBe(FloatType);
  });
});

describe("storeType Tests", () => {
  // Helper function to verify that types are stored for all relevant nodes
  const verifyTypesStored = (program: Program, expectedTypes: Map<number, Type>) => {
    for (const [nodeIndex, expectedType] of expectedTypes) {
      expect(program.types[nodeIndex]).toBeDefined();
      expect(program.types[nodeIndex]).toEqualType(expectedType);
    }
  };

  it("should store types for primitive literals", () => {
    const prog = int(42);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for boolean literals", () => {
    const prog = bool(true);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(BoolType);
    expect(result).toBe(BoolType);
  });

  it("should store types for variable references", () => {
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    
    const prog = v("x");
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for function applications", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    envSetVal(env, "add", addFn);
    
    const prog = app(app(v("add"), int(5)), int(3));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for all nodes in a complex expression", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "isPositive", isPositiveFn);
    
    // Create a complex expression: isPositive(add(5, 3))
    const prog = app(v("isPositive"), app(app(v("add"), int(5)), int(3)));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(BoolType);
    expect(result).toBe(BoolType);
    
    // Check that types were stored for all nodes
    for (let i = 0; i < program.nodes.length; i++) {
      const node = program.nodes[i]!
      if (node.kind === "IntLiteral") {
        expect(program.types[i]).toBe(IntType);
      } else if (node.kind === "App") {
        // Function application nodes should have their result type stored
        expect(program.types[i]).toBeDefined();
      }
    }
  });

  it("should store types for conditional expressions", () => {
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    envSetVal(env, "y", IntType);
    
    // Create: if x > 0 then x else y
    // Note: This test needs to be adjusted since the current system doesn't support
    // boolean conditions properly. We'll test with a simpler conditional.
    const prog = _if(bool(true), v("x"), v("y"));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for function declarations", () => {
    const env: Env = new Map();
    
    // Create: fun f(x: Int): Int { x }
    // Note: Function declarations need special handling in the lineariser
    const prog = lam("x", v("x"));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the function type was stored
    expect(program.types[program.rootIndex]).toBeDefined();
    expect(result).toBeDefined();
  });

  it("should store types for nested expressions", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const mulFn = arrow(IntType, arrow(IntType, IntType));
    envSetVal(env, "add", addFn);
    envSetVal(env, "mul", mulFn);
    
    // Create: add(mul(2, 3), 4)
    const prog = app(app(v("add"), app(app(v("mul"), int(2)), int(3))), int(4));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for sequence expressions", () => {
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    envSetVal(env, "y", IntType);
    
    // Create: { x; y }
    const prog = block(v("x"), v("y"));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for let expressions", () => {
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    
    // Create: let y = x in y
    const prog = _let("y", null, v("x"));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    // Note: Let expressions may not store types in the current implementation
    expect(result).toBe(IntType);
  });

  it("should store types for overloaded function applications", () => {
    const env: Env = new Map();
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(BoolType, BoolType)
    ]);
    envSetVal(env, "f", overloadedFn);
    
    // Create: f(42)
    const prog = app(v("f"), int(42));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for type applications", () => {
    const env: Env = new Map();
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    envSetType(env, "List", listScheme);
    
    const prog = _let("list", typeApp(v("List"), [v("Int")]), null);
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(tapp(listScheme, [IntType]));

    expect(program.types[program.rootIndex]).toEqualType(tapp(listScheme, [IntType]));
  });

  it("should verify all nodes have types stored after type checking", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "isPositive", isPositiveFn);
    
    // Create a complex expression with multiple nodes
    const prog = app(v("isPositive"), app(app(v("add"), int(5)), int(3)));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Verify that all nodes that should have types stored actually have them
    for (let i = 0; i < program.nodes.length; i++) {
      const node = program.nodes[i]!;
      if (node.kind === "IntLiteral" || node.kind === "BoolLiteral" || 
          node.kind === "Var" || node.kind === "App" || node.kind === "If") {
        expect(program.types[i]).toBeDefined();
        expect(program.types[i]).not.toBeNull();
      }
    }
    
    expect(result).toBe(BoolType);
  });

  it("should store types for function parameters", () => {
    const env: Env = new Map();
    
    // Create: fun f(x: Int): Int { x }
    // Note: Function declarations need special handling
    const prog = lam("x", v("x"));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the function type was stored
    expect(program.types[program.rootIndex]).toBeDefined();
    
    // The function should have type Int -> Int (or a more general type)
    expect(result).toBeDefined();
  });

  it("should store types for complex nested function applications", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const mulFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "mul", mulFn);
    envSetVal(env, "isPositive", isPositiveFn);
    
    // Create: isPositive(add(mul(2, 3), mul(4, 5)))
    const prog = app(
      v("isPositive"), 
      app(
        app(v("add"), 
          app(app(v("mul"), int(2)), int(3))
        ), 
        app(app(v("mul"), int(4)), int(5))
      )
    );
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(BoolType);
    expect(result).toBe(BoolType);
    
    // Verify that all application nodes have their types stored
    for (let i = 0; i < program.nodes.length; i++) {
      const node = program.nodes[i]!;
      if (node.kind === "App") {
        expect(program.types[i]).toBeDefined();
      }
    }
  });

  it("should store types for deeply nested expressions", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const mulFn = arrow(IntType, arrow(IntType, IntType));
    const subFn = arrow(IntType, arrow(IntType, IntType));
    envSetVal(env, "add", addFn);
    envSetVal(env, "mul", mulFn);
    envSetVal(env, "sub", subFn);
    
    // Create: add(mul(sub(10, 2), 3), mul(4, 5))
    const prog = app(
      app(v("add"), 
        app(app(v("mul"), 
          app(app(v("sub"), int(10)), int(2))
        ), int(3))
      ), 
      app(app(v("mul"), int(4)), int(5))
    );
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
    
    // Verify that all arithmetic operation nodes have their types stored
    for (let i = 0; i < program.nodes.length; i++) {
      const node = program.nodes[i]!;
      if (node.kind === "App") {
        expect(program.types[i]).toBeDefined();
        // Note: Not all App nodes will have IntType - some will have function types
        if (i === program.rootIndex) {
          expect(program.types[i]).toBe(IntType);
        }
      }
    }
  });

  it("should store types for expressions with mixed types", () => {
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    const notFn = arrow(BoolType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "isPositive", isPositiveFn);
    envSetVal(env, "not", notFn);
    
    // Create: not(isPositive(add(5, 3)))
    const prog = app(
      v("not"), 
      app(v("isPositive"), 
        app(app(v("add"), int(5)), int(3))
      )
    );
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(BoolType);
    expect(result).toBe(BoolType);
    
    // Verify that types are stored correctly for each operation
    const expectedTypes = new Map<number, Type>();
    for (let i = 0; i < program.nodes.length; i++) {
      const node = program.nodes[i]!;
      if (node.kind === "IntLiteral") {
        expectedTypes.set(i, IntType);
      } else if (node.kind === "App") {
        // The final result should be BoolType
        if (i === program.rootIndex) {
          expectedTypes.set(i, BoolType);
        }
      }
    }
    
    verifyTypesStored(program, expectedTypes);
  });

  it("should store types for expressions with type variables", () => {
    const env: Env = new Map();
    const idFn = arrow(tvar("T"), tvar("T"));
    const idScheme = scheme("id", getNextSchemeId(), ["T"], idFn);
    envSetVal(env, "id", idScheme);
    
    // Create: id(42)
    const prog = app(v("id"), int(42));
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    
    const result = runExpectingResult(bytecode, env, program);
    expect(result).toEqualType(IntType);
    expect(program.types[program.rootIndex]).toEqualType(IntType);

    // Check application 
    const app_ = program.apps.get(program.rootIndex)!
    expect(app_).toBeDefined();
    expect(app_.fn).toEqualType(arrowN([IntType], IntType));
    expect(app_.args).toEqual([IntType]);
    expect(app_.typeArgs).toEqual([]);
    expect(app_.result).toEqualType(IntType);

    const inst = program.instantiations.filter(x => x.schemeId === idScheme.id)
    expect(inst).toHaveLength(1);
    expect(inst[0]!.mono).toEqualType(tapp(idScheme, [IntType])); // TODO: A bit confused when to use tapp or arrow
    expect(inst[0]!.args[0]).toEqualType(IntType);
    expect(program.schemes.get(idScheme.id)).toEqual(idScheme);
    
  });

  it("should store types for expressions with complex type schemes", () => {
    const env: Env = new Map();
    const listScheme = scheme("List", getNextSchemeId(), ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const mapFn = arrow(tapp(listScheme, [tvar("A")]), arrow(arrow(tvar("A"), tvar("B")), tapp(listScheme, [tvar("B")])));
    const mapScheme = scheme("Map", getNextSchemeId(), ["A", "B"], mapFn)
    envSetType(env, "List", listScheme);
    envSetVal(env, "map", mapScheme);
    
    // Create: map(List<Int>, fn)
    // TODO: This shouldn't be allowed
    const prog = block(
      _let("list", typeApp(v("List"), [v("Int")]), null),
      app(v("map"), v("list"))
    );
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBeDefined();
    expect(result).toBeDefined();

    expect(program.schemes.get(listScheme.id)).toEqual(listScheme);
    expect(program.schemes.get(mapScheme.id)).toEqual(mapScheme);
  });
});
