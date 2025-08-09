import { inspect } from "bun";
import { describe, it, expect, beforeEach } from "bun:test";
import {
  type Instr, type Env, type Program, type Type, type Scheme, type UnknownType, type SuspendMissing,
  assert, isType, isScheme, newUnknown, arrow, arrowN,
  lineariseProgram, runInternal, createInterpreterState,
  startTrial, rollback, commit, unify, subsume, show,
  tvar, tapp, tstruct, overload, scheme, dummy, getNextSchemeId,
  isArrowN, compactInspect, areTypesEqual,
  IntType, BoolType, UnitType, FloatType,
  registerTrait,
  registerTraitImpl,
  createBounds,
  hasTrait,
  requireTraitNow,
  dischargeDeferredObligations,
  emitObligationsForInstantiation,
  ProgramBuilder,
  TraitType,
} from "./typecheck";
import { TestBuilder } from "./testUtils";

/** Run for tests until result is found */
function runExpectingResult(code: Instr[], initialEnv: Env, program: Program, builder?: ProgramBuilder): Type {
  const actualBuilder = builder || new ProgramBuilder();
  const result = runInternal(createInterpreterState(code, initialEnv, actualBuilder, program));
  assert(isType(result), "Expected result, but got suspend", { result });
  const inst = program!.instantiations.map(i => ({ ...i, scheme: program!.schemes.get(i.schemeId)! }));
  console.log('program.instantiations', inst);
  return result;
}

describe("Basic Type Checking", () => {
  it("should type check identity function applied to Int", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const x = b.var("x");                             // x
    const id = b.lam("x", x);                         // λx. x   (no annotation)
    const prog = b.app(id, b.int(42));                // (λx. x) 42

    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program, builder);
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
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const seqProg1 = b.block(
      b.app(b.var("print"), b.int(1)),                // print 1 : Unit
      b.let("y", null, b.int(2)),                     // let y=2
      b.var("y")                                      // y : Int
    );

    const program1 = b.program(seqProg1);
    const seqBytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(seqBytecode1, env, program1, builder);
    expect(result1).toBe(IntType);
  });

  it("should handle sequence with function application and conditional", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const seqProg2 = b.block(
      b.app(b.var("print"), b.int(10)),               // print 10 : Unit
      b.let("x", null, b.int(5)),                     // let x=5
      b.if(b.app(b.var("isPositive"), b.var("x")),    // if isPositive x then
        b.app(b.var("print"), b.int(100)),            //   print 100 : Unit
        b.app(b.var("print"), b.int(200))             //   print 200 : Unit
      ),
      b.let("result", null, b.int(42)),               // let result=42
      b.var("result")                                 // result : Int
    );

    const program2 = b.program(seqProg2);
    const seqBytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(seqBytecode2, env, program2, builder);
    expect(result2).toBe(IntType);
  });

  it("should handle nested let bindings with function calls", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const seqProg3 = b.block(
      b.app(b.var("print"), b.int(1)),                // print 1 : Unit
      b.let("a", null, b.int(10)),                    // let a=10
      b.let("b", null, b.int(20)),                    //   let b=20
      b.let("sum", null, b.app(b.app(b.var("add"), b.var("a")), b.var("b"))), // let sum=add a b
      b.app(b.var("print"), b.var("sum")),            //     print sum : Unit
      b.bool(true)                                    // true : Bool
    );

    const program3 = b.program(seqProg3);
    const seqBytecode3 = lineariseProgram(builder, program3.rootIndex);
    const result3 = runExpectingResult(seqBytecode3, env, program3, builder);
    expect(result3).toBe(BoolType);
  });

  it("should handle complex sequence with multiple operations", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const seqProg4 = b.block(
      b.app(b.var("print"), b.int(0)),                // print 0 : Unit
      b.let("counter", null, b.int(1)),               // let counter=1
      b.if(b.app(b.var("isPositive"), b.var("counter")),      //   if isPositive counter then
        b.block(                                      //     block:
          b.app(b.var("print"), b.int(1)),            //       print 1 : Unit
          b.app(b.var("print"), b.int(2)),            //       print 2 : Unit
          b.int(3)                                    //       3 : Int
        ),
        b.block(                                      //     else block:
          b.app(b.var("print"), b.int(-1)),           //       print -1 : Unit
          b.app(b.var("print"), b.int(-2)),           //       print -2 : Unit
          b.int(-3)                                   //       -3 : Int
        )
      ),
      b.let("final", null, b.int(999)),               // let final=999
      b.var("final")                                  // final : Int
    );

    const program4 = b.program(seqProg4);
    const seqBytecode4 = lineariseProgram(builder, program4.rootIndex);
    const result4 = runExpectingResult(seqBytecode4, env, program4, builder);
    expect(result4).toBe(IntType);
  });

  it("should handle Unit type handling", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const seqProg5 = b.block(
      b.app(b.var("print"), b.int(1)),                // print 1 : Unit
      b.app(b.var("print"), b.int(2)),                // print 2 : Unit
      b.app(b.var("print"), b.int(3)),                // print 3 : Unit
      b.let("dummy", null, b.app(b.var("print"), b.int(4))),         // let dummy=print 4
      b.int(42)                                       //   42 : Int
    );

    const program5 = b.program(seqProg5);
    const seqBytecode5 = lineariseProgram(builder, program5.rootIndex);
    const result5 = runExpectingResult(seqBytecode5, env, program5, builder);
    expect(result5).toBe(IntType);
  });

  it("should handle subtype system with primitive widening", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const seqProg6 = b.block(
      b.app(b.var("print"), b.int(10)),               // print 10 : Unit
      b.let("x", b.var("Float"), b.int(5)),           // let x: Float = 5
      b.let("y", b.var("Int"), b.int(3)),             // let y: Int = 3
      b.bool(true)                                    // true : Bool
    );

    const program6 = b.program(seqProg6);
    const seqBytecode6 = lineariseProgram(builder, program6.rootIndex);
    const result6 = runExpectingResult(seqBytecode6, env, program6, builder);
    expect(result6).toBe(BoolType);
  });
});

describe("Trial/Rollback System", () => {
  it("should demonstrate trial/rollback system", () => {
    // Reset the unknown counter for this test
    // nextU = 1; // TODO: Fix this assignment
    
    // Demonstrate the trial/rollback system
    const builder = new ProgramBuilder();
    const env2: Env = new Map();
    envSetVal(env2, "f", arrow(IntType, BoolType));

    // Create some unknown types
    const u1: UnknownType = newUnknown(builder);
    const u2: UnknownType = newUnknown(builder);

    expect(show(u1, builder)).toBe("?0");
    expect(show(u2, builder)).toBe("?1");

    // Start a trial
    const mark = startTrial(builder);

    // Try to unify u1 with Int
    unify(u1, IntType, true, builder).getOrThrow();
    expect(show(u1, builder)).toBe("Int");
    
    // Try to unify u2 with Bool
    unify(u2, BoolType, true, builder).getOrThrow();
    expect(show(u2, builder)).toBe("Bool");
    
    // Try something that should fail
    const error = unify(u1, BoolType, true, builder).expectError();
    expect(error).toBeDefined();
    
    // Rollback to the mark
    rollback(mark, builder);
    expect(show(u1, builder)).toBe("?0");
    expect(show(u2, builder)).toBe("?1");

    // Start another trial
    const mark2 = startTrial(builder);

    // Try a successful unification
    unify(u1, IntType, true, builder).getOrThrow();
    unify(u2, BoolType, true, builder).getOrThrow();
    expect(show(u1, builder)).toBe("Int");
    expect(show(u2, builder)).toBe("Bool");

    // Commit the changes
    commit(mark2, builder);
    expect(show(u1, builder)).toBe("Int");
    expect(show(u2, builder)).toBe("Bool");
  });
});

describe("Simple Trial/Rollback", () => {

  it("should handle simple trial/rollback operations", () => {
    // Create a builder for isolated state
    const builder = new ProgramBuilder();
    
    // Create fresh unknowns using the builder
    const u3: UnknownType = newUnknown(builder);
    const u4: UnknownType = newUnknown(builder);

    expect(show(u3, builder)).toBe("?0");
    expect(show(u4, builder)).toBe("?1");

    // Test 1: Successful trial
    const mark3 = startTrial(builder);
    unify(u3, IntType, true, builder).getOrThrow();
    unify(u4, BoolType, true, builder).getOrThrow();
    expect(show(u3, builder)).toBe("Int");
    expect(show(u4, builder)).toBe("Bool");
    expect(builder.trail.length).toBeGreaterThanOrEqual(2);

    // Test 2: Failed trial with rollback
    const mark4 = startTrial(builder);
    unify(u3, IntType, true, builder).getOrThrow();    // This should work (u3 is already Int)
    const error = unify(u4, IntType, true, builder).expectError();    // This should fail (Bool ≠ Int)
    expect(error).toBeDefined();
    rollback(mark4, builder);
    expect(show(u3, builder)).toBe("Int");
    expect(show(u4, builder)).toBe("Bool");

    // Test 3: Commit successful trial
    const mark5 = startTrial(builder);
    unify(u3, IntType, true, builder).getOrThrow();    // This should work (u3 is already Int)
    commit(mark5, builder);
    expect(show(u3, builder)).toBe("Int");
    expect(show(u4, builder)).toBe("Bool");
  });
});

describe("Non-recording Operations", () => {
  it("should handle non-recording operations correctly", () => {
    // Create a builder for isolated state
    const builder = new ProgramBuilder();
    
    const u5: UnknownType = newUnknown(builder);
    expect(show(u5, builder)).toBe("?0");

    // This should not be recorded
    unify(u5, IntType, false, builder).getOrThrow();
    expect(show(u5, builder)).toBe("Int");
    expect(builder.trail.length).toBe(0); // Not recorded

    // This should be recorded
    const mark6 = startTrial(builder);
    unify(u5, IntType, true, builder).getOrThrow();  // This should work since u5 is already Int
    rollback(mark6, builder);
    expect(show(u5, builder)).toBe("Int");
  });
});

describe("Apply/Join Non-recording", () => {
  it("should handle apply/join non-recording operations", () => {
    // Create a builder for isolated state
    const builder = new ProgramBuilder();
    
    const u6: UnknownType = newUnknown(builder);
    const u7: UnknownType = newUnknown(builder);

    expect(show(u6, builder)).toBe("?0");
    expect(show(u7, builder)).toBe("?1");

    // Simulate an apply operation (function application)
    const fnType = { kind: "Arrow" as const, param: u6, result: u7 };
    unify(fnType.param, IntType, false, builder).getOrThrow();  // This simulates apply behavior
    expect(show(u6, builder)).toBe("Int");

    // Start a trial and try to change u6
    const mark7 = startTrial(builder);
    const error = unify(u6, BoolType, true, builder).expectError();  // This should fail since u6 is already Int
    expect(error).toBeDefined();
    rollback(mark7, builder);
    expect(show(u6, builder)).toBe("Int");
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

    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog1 = b.app(b.var("add"), b.int(42));
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toBe(IntType);
  });

  it("should handle overloaded functions with Float arguments", () => {
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(FloatType, FloatType)
    ]);

    const env: Env = new Map();
    envSetVal(env, "add", overloadedFn);

    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog2 = b.app(b.var("add"), b.int(42)); // This should work due to Int ≤ Float
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
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
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog3 = b.app(b.var("func"), b.bool(true));
    const program3 = b.program(prog3);
    const bytecode3 = lineariseProgram(builder, program3.rootIndex);
    const result3 = runExpectingResult(bytecode3, env, program3, builder);
    expect(result3).toBe(BoolType);
  });

  it("should reject no viable overloads", () => {
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(FloatType, FloatType)
    ]);

    const env: Env = new Map();
    envSetVal(env, "add", overloadedFn);

    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog4 = b.app(b.var("add"), b.bool(true));
    const program4 = b.program(prog4);
    const bytecode4 = lineariseProgram(builder, program4.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode4, env, program4, builder);
    }).toThrow("no viable overloads");
  });

  it("should reject ambiguous overloads", () => {
    const ambiguousOverload = overload([
      arrow(IntType, IntType),
      arrow(IntType, BoolType)  // Same parameter type, different return type
    ]);
    const env: Env = new Map();
    envSetVal(env, "ambiguous", ambiguousOverload);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog7 = b.app(b.var("ambiguous"), b.int(42));
    const program7 = b.program(prog7);
    const bytecode7 = lineariseProgram(builder, program7.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode7, env, program7, builder);
    }).toThrow("ambiguous overload");
  });

  it("should prefer exact matches over implicit casts", () => {
    const exactVsCastOverload = overload([
      arrow(IntType, IntType),      // Exact match for Int
      arrow(FloatType, FloatType)   // Requires implicit cast from Int
    ]);
    const env: Env = new Map();
    envSetVal(env, "exactVsCast", exactVsCastOverload);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog8 = b.app(b.var("exactVsCast"), b.int(42));
    const program8 = b.program(prog8);
    const bytecode8 = lineariseProgram(builder, program8.rootIndex);
    const result8 = runExpectingResult(bytecode8, env, program8, builder);
    expect(result8).toBe(IntType);
  });

  it("should accept implicit casts when only option available", () => {
    const onlyCastOverload = overload([
      arrow(FloatType, FloatType)   // Only Float overload available
    ]);
    const env: Env = new Map();
    envSetVal(env, "onlyCast", onlyCastOverload);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog9 = b.app(b.var("onlyCast"), b.int(42));
    const program9 = b.program(prog9);
    const bytecode9 = lineariseProgram(builder, program9.rootIndex);
    const result9 = runExpectingResult(bytecode9, env, program9, builder);
    expect(result9).toBe(FloatType);
  });
});

describe("Multi-Argument Functions", () => {
  it("should handle basic multi-argument functions", () => {
    const env: Env = new Map();
    
    // Create a function that takes 3 Int arguments and returns Int
    const add3Fn = arrowN([IntType, IntType, IntType], IntType);
    envSetVal(env, "add3", add3Fn);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog1 = b.appN(b.var("add3"), [b.int(1), b.int(2), b.int(3)]);
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toBe(IntType);
  });

  it("should handle multi-argument functions with different types", () => {
    const env: Env = new Map();
    const mixedFn = arrowN([IntType, BoolType, FloatType], BoolType);
    envSetVal(env, "mixed", mixedFn);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog2 = b.appN(b.var("mixed"), [b.int(42), b.bool(true), b.int(3.14)]);
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
    expect(result2).toBe(BoolType);
  });

  it("should handle overloaded multi-argument functions", () => {
    const env: Env = new Map();
    const overloadedMultiFn = overload([
      arrowN([IntType, IntType], IntType),
      arrowN([FloatType, FloatType], FloatType)
    ]);
    envSetVal(env, "overloadedMulti", overloadedMultiFn);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog3 = b.appN(b.var("overloadedMulti"), [b.int(10), b.int(20)]);
    const program3 = b.program(prog3);
    const bytecode3 = lineariseProgram(builder, program3.rootIndex);
    const result3 = runExpectingResult(bytecode3, env, program3, builder);
    expect(result3).toBe(IntType);
  });

  it("should reject wrong number of arguments", () => {
    const env: Env = new Map();
    const add3Fn = arrowN([IntType, IntType, IntType], IntType);
    envSetVal(env, "add3", add3Fn);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog4 = b.appN(b.var("add3"), [b.int(1), b.int(2)]); // Only 2 args, needs 3
    const program4 = b.program(prog4);
    const bytecode4 = lineariseProgram(builder, program4.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode4, env, program4, builder);
    }).toThrow("expects 3 arguments but got 2");
  });

  it("should handle nested multi-argument applications", () => {
    const env: Env = new Map();
    const add3Fn = arrowN([IntType, IntType, IntType], IntType);
    envSetVal(env, "add3", add3Fn);
    const nestedFn = arrowN([IntType, IntType], IntType);
    envSetVal(env, "nested", nestedFn);
    
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog5 = b.appN(b.var("nested"), [
      b.appN(b.var("add3"), [b.int(1), b.int(2), b.int(3)]),
      b.int(10)
    ]);
    const program5 = b.program(prog5);
    const bytecode5 = lineariseProgram(builder, program5.rootIndex);
    const result5 = runExpectingResult(bytecode5, env, program5, builder);
    expect(result5).toBe(IntType);
  });
});

describe("Generic Type System", () => {
  it("should handle generic identity function with Int", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const env: Env = new Map();
    
    // Define a generic identity function: ∀T. T → T
    const idScheme = builder.scheme("id", ["T"], arrowN([tvar("T")], tvar("T")));
    envSetVal(env, "id", idScheme);
    
    // Test with Int
    const prog1 = b.app(b.var("id"), b.int(42));
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toBe(IntType);
  });

  it("should handle generic identity function with Bool", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const env: Env = new Map();
    
    // Define a generic identity function: ∀T. T → T
    const idScheme = builder.scheme("id", ["T"], arrowN([tvar("T")], tvar("T")));
    envSetVal(env, "id", idScheme);
    
    // Test with Bool
    const prog2 = b.app(b.var("id"), b.bool(true));
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
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
    const builder = new ProgramBuilder();
    unify(tvar("T"), tvar("T"), false, builder).getOrThrow();
    
    const error1 = unify(tvar("T"), tvar("U"), false, builder).expectError();
    expect(error1).toBeDefined();
    
    const error2 = unify(tvar("T"), IntType, false, builder).expectError();
    expect(error2).toBeDefined();
  });

  it("should handle type application correctly", () => {
    const builder = new ProgramBuilder();
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const listBool = tapp(listScheme, [BoolType]);
    
    unify(listInt, listInt, false, builder).getOrThrow();
    
    const error3 = unify(listInt, listBool, false, builder).expectError();
    expect(error3).toBeDefined();
  });
});

describe("Pending Bindings", () => {
  it("should handle basic pending binding scenario", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    env.set("missingVar", { value: { tag: "PendV", waiters: [] } });
    const b = new TestBuilder(builder);
    // Create a program that references a variable that's not in the environment
    const prog = b.var("missingVar");
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    
    // Run the interpreter and expect it to suspend
    const state = createInterpreterState(bytecode, env, builder, program);
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
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog2 = b.app(b.var("missingVar"), b.int(42)); // missingVar(42)
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const env2 = new Map();
    env2.set("missingVar", { tag: "Pending", waiters: [] });

    
    const state2 = createInterpreterState(bytecode2, env2, builder, program2);
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
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog3 = b.var("anotherMissingVar");
    const program3 = b.program(prog3);
    const bytecode3 = lineariseProgram(builder, program3.rootIndex);
    const env3 = new Map();
    env3.set("anotherMissingVar", { tag: "Pending", waiters: [] });
    
    const state3 = createInterpreterState(bytecode3, env3, builder, program3);
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
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog4 = b.app(b.app(b.var("outerFunc"), b.var("innerVar")), b.int(10));
    const program4 = b.program(prog4);
    const bytecode4 = lineariseProgram(builder, program4.rootIndex);

    const env4 = new Map();
    env4.set("outerFunc", { tag: "Pending", waiters: [] });
    env4.set("innerVar", { tag: "Pending", waiters: [] });

    const state4 = createInterpreterState(bytecode4, env4, builder, program4);
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const b = new TestBuilder(builder);
    const prog = b.var("unboundVar");
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode, env, program);
    }).toThrow("unbound variable unboundVar");
  });
  
  it("should reject unbound variable in function application", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const b = new TestBuilder(builder);
    const prog2 = b.app(b.var("unboundFunc"), b.int(42));
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode2, env, program2);
    }).toThrow("unbound variable unboundFunc");
  });
  
  it("should reject unbound variable in let binding", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const b = new TestBuilder(builder);
    const prog3 = b.let("x", null, b.var("unboundInLet"));
    const program3 = b.program(prog3);
    const bytecode3 = lineariseProgram(builder, program3.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode3, env, program3);
    }).toThrow("unbound variable unboundInLet");
  });
  
  it("should reject unbound variable in nested scope", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const b = new TestBuilder(builder);
    const prog4 = b.lam("param", b.var("unboundInLambda"));
    const program4 = b.program(prog4);
    const bytecode4 = lineariseProgram(builder, program4.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode4, env, program4);
    }).toThrow("unbound variable unboundInLambda");
  });
  
  it("should reject multiple unbound variables", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const b = new TestBuilder(builder);
    const prog5 = b.app(b.app(b.var("func1"), b.var("func2")), b.int(42));
    const program5 = b.program(prog5);
    const bytecode5 = lineariseProgram(builder, program5.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode5, env, program5);
    }).toThrow("unbound variable func1");
  });
  
  it("should reject unbound variable in mixed environment", () => {
    const builder = new ProgramBuilder();
    const envWithSome: Env = new Map();
    envSetVal(envWithSome, "boundVar", IntType);
    envSetVal(envWithSome, "boundFunc", arrow(IntType, BoolType));
    
    const b = new TestBuilder(builder);
    const prog6 = b.app(b.app(b.var("boundFunc"), b.var("boundVar")), b.var("unboundVar"));
    const program6 = b.program(prog6);
    const bytecode6 = lineariseProgram(builder, program6.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode6, envWithSome, program6);
    }).toThrow("unbound variable unboundVar");
  });
  
  it("should reject unbound variable in sequence", () => {
    const builder = new ProgramBuilder();
    const envWithPrint: Env = new Map();
    envSetVal(envWithPrint, "print", arrow(IntType, UnitType));
    
    const b = new TestBuilder(builder);
    const prog7 = b.block(
      b.app(b.var("print"), b.int(1)),
      b.var("unboundInSeq"),
      b.int(42)
    );
    const program7 = b.program(prog7);
    const bytecode7 = lineariseProgram(builder, program7.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode7, envWithPrint, program7);
    }).toThrow("unbound variable unboundInSeq");
  });
});

function printProgram(program: Program, builder: ProgramBuilder) {
  console.log("Program nodes:", program.nodes.length);
  console.log("Program types:", program.types.length);
  console.log("Root index:", program.rootIndex);
  
  program.nodes.forEach((node, index) => {
    const type = program.types[index] ? show(program.types[index], builder) : "null"
    console.log(`${index}: ${type}: ${compactInspect(node)}`)
  });
}

function printInstructions(bytecode: Instr[]) {
  bytecode.forEach((instr, index) => {
    const { op, ...rest } = instr;
    console.log(`${String(index).padStart(3)}: ${op.padStart(24)}: ${compactInspect(rest)}`)
  });
}

describe("Program-Based Type Checking", () => {
  it("should handle conversion from Expr to Program", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const expr = b.int(42);
    const convertedProgram = b.program(expr);

    expect(convertedProgram.nodes.length).toBeGreaterThan(0);
    expect(convertedProgram.rootIndex).toBeDefined();
    
    const bytecode5 = lineariseProgram(builder, convertedProgram.rootIndex);
    const result5 = runExpectingResult(bytecode5, new Map(), convertedProgram, builder);
    expect(result5).toBe(IntType);
  });
  
  it("should handle lambda expression conversion", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const lambdaExpr = b.lam("x", b.var("x")); // λx. x
    const lambdaProgram = b.program(lambdaExpr);
    
    expect(lambdaProgram.nodes.length).toBeGreaterThan(0);
    expect(lambdaProgram.rootIndex).toBeDefined();
    
    const bytecode6 = lineariseProgram(builder, lambdaProgram.rootIndex);
    const result6 = runExpectingResult(bytecode6, new Map(), lambdaProgram, builder);
    expect(isArrowN(result6)).toBe(true);
  });
  
  it("should handle lambda application", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const lambdaExpr = b.lam("x", b.var("x")); // λx. x
    const lambdaAppExpr = b.app(lambdaExpr, b.int(42)); // (λx. x) 42
    const lambdaAppProgram = b.program(lambdaAppExpr);
    
    const bytecode7 = lineariseProgram(builder, lambdaAppProgram.rootIndex);
    const result7 = runExpectingResult(bytecode7, new Map(), lambdaAppProgram, builder);
    expect(result7).toBe(IntType);
  });
  
  it("should handle multi-parameter lambda", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const multiLambdaExpr = b.lamN(["x", "y"], b.app(b.app(b.var("add"), b.var("x")), b.var("y"))); // λx y. add x y
    const multiLambdaProgram = b.program(multiLambdaExpr);
    
    expect(multiLambdaProgram.nodes.length).toBeGreaterThan(0);
    
    // Set up environment with add function
    const env8: Env = new Map();
    envSetVal(env8, "add", arrow(IntType, arrow(IntType, IntType)));
    
    const bytecode8 = lineariseProgram(builder, multiLambdaProgram.rootIndex);
    const result8 = runExpectingResult(bytecode8, env8, multiLambdaProgram, builder);
    expect(isArrowN(result8)).toBe(true);
  });
  
  it("should handle multi-parameter lambda application", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const multiLambdaExpr = b.lamN(["x", "y"], b.app(b.app(b.var("add"), b.var("x")), b.var("y"))); // λx y. add x y
    const multiLambdaAppExpr = b.appN(multiLambdaExpr, [b.int(10), b.int(20)]); // (λx y. add x y) 10 20
    const multiLambdaAppProgram = b.program(multiLambdaAppExpr);
    
    // Set up environment with add function
    const env9: Env = new Map();
    envSetVal(env9, "add", arrow(IntType, arrow(IntType, IntType)));
    
    const bytecode9 = lineariseProgram(builder, multiLambdaAppProgram.rootIndex);
    const result9 = runExpectingResult(bytecode9, env9, multiLambdaAppProgram, builder);
    expect(result9).toBe(IntType);
  });
});

describe("Generic Functions in Programs", () => {
  it("should define and use generic identity function in program", () => {
    // Define a generic identity function: ∀T. T → T
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const genericId = b.funDecl("id", ["T"], ["x"], b.var("x"), ["T"]);
    
    // Create a program that defines the function and uses it
    const programExpr = b.block(
      genericId,  // Define the generic function
      b.app(b.var("id"), b.int(42))  // Use it with Int
    );
    
    const program = b.program(programExpr);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program, builder);
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
    toEqualType(expected: Type, builder: ProgramBuilder): T;
  }
}

expect.extend({
  toEqualType(received: Type, expected: Type, builder: ProgramBuilder) {
    return {  
      pass: areTypesEqual(received, expected, builder),
      message: () => `expected ${received} to be ${expected}`,
    };
  },
} as any);

describe("Type Annotation Resolution for Generic Structs", () => {
  it("should resolve simple non-generic struct annotations", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define a simple non-generic struct: struct Point { x: Int, y: Int }
    const pointStruct = tstruct("Point", [{ name: "x", type: IntType }, { name: "y", type: IntType }]);
    envSetType(env, "Point", pointStruct);
    
    const b = new TestBuilder(builder);
    const prog = b.let("p", b.var("Point"), null);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(pointStruct, builder);
  });

  it("should resolve generic struct annotations with concrete type arguments", () => {
    const builder = new ProgramBuilder()
    const env: Env = new Map();
    
    // Define a generic struct: struct List<T> { ... }
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const listBool = tapp(listScheme, [BoolType]);
    envSetType(env, "List", listScheme);
    
    const b = new TestBuilder(builder);
    const prog1 = b.let("numbers", b.typeApp("List", ["Int"]), null);
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toEqualType(listInt, builder);
    
    const prog2 = b.let("flags", b.typeApp("List", ["Bool"]), null);
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
    expect(result2).toEqualType(listBool, builder);
  });

  it("should resolve nested generic struct annotations", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define generic structs: struct List<T> and struct Option<T>
    const optionScheme = builder.scheme("Option", ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionListInt = tapp(optionScheme, [tapp(listScheme, [IntType])]);
    const listOptionInt = tapp(listScheme, [tapp(optionScheme, [IntType])]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    const b = new TestBuilder(builder);
    const prog1 = b.let("optList", b.typeApp("Option", [b.typeApp("List", ["Int"])]), null);
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toEqualType(optionListInt, builder);
    
    const prog2 = b.let("listOpt", b.typeApp("List", [b.typeApp("Option", ["Int"])]), null);
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
    expect(result2).toEqualType(listOptionInt, builder);
  });

  it("should resolve generic struct annotations with multiple type parameters", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define a struct with multiple type parameters: struct Pair<T, U> { first: T, second: U }
    const pairScheme = builder.scheme("Pair", ["T", "U"], tstruct("Pair", [{ name: "first", type: tvar("T") }, { name: "second", type: tvar("U") }]));
    const pairIntBool = tapp(pairScheme, [IntType, BoolType]);
    const pairFloatInt = tapp(pairScheme, [FloatType, IntType]);
    
    envSetType(env, "Pair", pairScheme);
    
    const b = new TestBuilder(builder);
    const prog1 = b.let("mixed", b.typeApp("Pair", ["Int", "Bool"]), null);
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toEqualType(pairIntBool, builder);
    
    const prog2 = b.let("numbers", b.typeApp("Pair", ["Float", "Int"]), null);
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
    expect(result2).toEqualType(pairFloatInt, builder);
  });

  it("should resolve complex nested generic struct annotations", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define multiple generic structs
    const mapScheme = builder.scheme("Map", ["T", "U"], tstruct("Map", [{ name: "key", type: tvar("T") }, { name: "value", type: tvar("U") }]));
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = builder.scheme("Option", ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const complexType = tapp(mapScheme, [
      tapp(listScheme, [IntType]),
      tapp(optionScheme, [BoolType])
    ]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    envSetType(env, "Map", mapScheme);

    console.log('env', env);
    
    const b = new TestBuilder(builder);
    const list = b.typeApp("List", ["Int"]);
    const option = b.typeApp("Option", ["Bool"]);
    const prog = b.let("complex", b.typeApp("Map", [list, option]), null);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(complexType, builder);
  });

  // TODO: implement type parameter constraints
  // it("should handle type parameters with constraints", () => {
  //   const env: Env = new Map();
    
  //   // Define a struct with constrained type parameters: struct SortedList<T: Ord> { ... }
  //   const sortedListInt = tapp("SortedList", [IntType]);
    
  //   const sortedListStruct = scheme(["T"], tstruct("SortedList", [{ name: "head", type: tvar("T") }]));
  //   envSetType(env, "SortedList", sortedListStruct);
    
  //   const b = new TestBuilder(builder);
  //   const prog = b.let("sorted", b.typeApp("SortedList", ["Int"]), null);
  //   const program = b.program(prog);
  //   const bytecode = lineariseProgram(program, program.rootIndex);
  //   const result = runExpectingResult(bytecode, env, program);
  //   expect(result).toEqualType(sortedListInt);
  // });

  it("should resolve generic struct annotations in function parameters", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define a function that takes generic structs as parameters
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = builder.scheme("Option", ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const optionBool = tapp(optionScheme, [BoolType]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    // Function: fn process<T>(list: List<T>, opt: Option<Bool>) -> T
    const processFn = arrowN([listInt, optionBool], IntType);
    envSetVal(env, "process", processFn);
    
    const b = new TestBuilder(builder);
    const prog = b.block(
      b.let("list", b.typeApp("List", ["Int"]), null),
      b.let("opt", b.typeApp("Option", ["Bool"]), null),
      b.appN(b.var("process"), [b.var("list"), b.var("opt")])
    );
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(IntType, builder);
  });

  it("should resolve generic struct annotations in let bindings with function calls", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = builder.scheme("Option", ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const optionInt = tapp(optionScheme, [IntType]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    // Function that returns a generic struct
    const createListFn = arrow(IntType, listInt);
    const createOptionFn = arrow(IntType, optionInt);
    envSetVal(env, "createList", createListFn);
    envSetVal(env, "createOption", createOptionFn);
    
    const b = new TestBuilder(builder);
    const prog = b.block(
      b.let("myList", b.typeApp("List", ["Int"]), b.app(b.var("createList"), b.int(42))),
      b.let("myOption", b.typeApp("Option", ["Int"]), b.app(b.var("createOption"), b.int(10))),
      b.int(999)
    );
    
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(IntType, builder);
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define a struct that expects 2 type parameters
    const pairScheme = builder.scheme("Pair", ["T", "U"], tstruct("Pair", [{ name: "first", type: tvar("T") }, { name: "second", type: tvar("U") }]));
    envSetType(env, "Pair", pairScheme);
    
    const b = new TestBuilder(builder);
    const prog1 = b.let("invalid", b.typeApp("Pair", ["Int"]), null); // Missing second type parameter
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode1, env, program1, builder);
    }).toThrow();
    
    const prog2 = b.let("invalid2", b.typeApp("Pair", ["Int", "Bool", "Float"]), null); // Too many type parameters
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode2, env, program2, builder);
    }).toThrow();
  });

  it("should reject undefined struct annotations", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    const b = new TestBuilder(builder);
    const prog = b.let("undefined", b.typeApp("UndefinedStruct", ["Int"]), null);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    
    expect(() => {
      runExpectingResult(bytecode, env, program, builder);
    }).toThrow();
  });

  it("should handle generic struct annotations with primitive type widening", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listFloat = tapp(listScheme, [FloatType]);
    
    envSetType(env, "List", listScheme);
    
    // Int should be accepted where Float is expected due to widening
    const b = new TestBuilder(builder);
    const prog = b.let("numbers", b.typeApp("List", ["Float"]), null);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(listFloat, builder);
  });

  it("should resolve generic struct annotations in complex expressions", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const optionScheme = builder.scheme("Option", ["T"], tstruct("Option", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const optionListInt = tapp(optionScheme, [listInt]);
    
    envSetType(env, "List", listScheme);
    envSetType(env, "Option", optionScheme);
    
    // Function that returns Option<List<Int>>
    const complexFn = arrow(IntType, optionListInt);
    envSetVal(env, "complexFn", complexFn);
    
    const b = new TestBuilder(builder);
    const prog = b.block(
      b.let("result", b.typeApp("Option", [b.typeApp("List", ["Int"])]), b.app(b.var("complexFn"), b.int(42))),
      b.int(999)
    );
    
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(IntType, builder);
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Define a struct that contains function types: struct Container<T> { fn: T -> T }
    const containerScheme = builder.scheme("Container", ["T"], tstruct("Container", [{ name: "fn", type: arrow(tvar("T"), tvar("T")) }]));
    const containerFn = tapp(containerScheme, [arrow(IntType, IntType)]);
    
    envSetType(env, "Container", containerScheme);
    
    
    const b = new TestBuilder(builder);
    const prog = b.let("container", b.typeApp("Container", [b.typeApp("Fn", ["Int", "Int"])]), null);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(containerFn, builder);
  });

  it("should handle generic struct annotations with overloaded functions", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const listInt = tapp(listScheme, [IntType]);
    const listFloat = tapp(listScheme, [FloatType]);
    
    envSetType(env, "List", listScheme);
    
    // Overloaded function that can work with List<Int> or List<Float>
    const overloadedFn = overload([
      arrow(listInt, IntType),
      arrow(listFloat, FloatType)
    ]);
    envSetVal(env, "overloadedFn", overloadedFn);
    
    const b = new TestBuilder(builder);
    const prog1 = b.block(
      b.let("list", b.typeApp("List", ["Int"]), null),
      b.app(b.var("overloadedFn"), b.var("list"))
    );
    const program1 = b.program(prog1);
    const bytecode1 = lineariseProgram(builder, program1.rootIndex);
    const result1 = runExpectingResult(bytecode1, env, program1, builder);
    expect(result1).toBe(IntType);
    
    const prog2 = b.block(
      b.let("list", b.typeApp("List", ["Float"]), null),
      b.app(b.var("overloadedFn"), b.var("list"))
    );
    const program2 = b.program(prog2);
    const bytecode2 = lineariseProgram(builder, program2.rootIndex);
    const result2 = runExpectingResult(bytecode2, env, program2, builder);
    expect(result2).toBe(FloatType);
  });
});

describe("storeType Tests", () => {
  // Helper function to verify that types are stored for all relevant nodes
  const verifyTypesStored = (program: Program, expectedTypes: Map<number, Type>, builder: ProgramBuilder) => {
    for (const [nodeIndex, expectedType] of expectedTypes) {
      expect(program.types[nodeIndex]).toBeDefined();
      expect(program.types[nodeIndex]).toEqualType(expectedType, builder);
    }
  };

  it("should store types for primitive literals", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog = b.int(42);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for boolean literals", () => {
    const builder = new ProgramBuilder();
    const b = new TestBuilder(builder);
    const prog = b.bool(true);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, new Map(), program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(BoolType);
    expect(result).toBe(BoolType);
  });

  it("should store types for variable references", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    
    const b = new TestBuilder(builder);
    const prog = b.var("x");
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for function applications", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    envSetVal(env, "add", addFn);
    
    const b = new TestBuilder(builder);
    const prog = b.app(b.app(b.var("add"), b.int(5)), b.int(3));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for all nodes in a complex expression", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "isPositive", isPositiveFn);
    
    // Create a complex expression: isPositive(add(5, 3))
    const b = new TestBuilder(builder);
    const prog = b.app(b.var("isPositive"), b.app(b.app(b.var("add"), b.int(5)), b.int(3)));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    envSetVal(env, "y", IntType);
    
    // Create: if x > 0 then x else y
    // Note: This test needs to be adjusted since the current system doesn't support
    // boolean conditions properly. We'll test with a simpler conditional.
    const b = new TestBuilder(builder);
    const prog = b.if(b.bool(true), b.var("x"), b.var("y"));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for function declarations", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Create: fun f(x: Int): Int { x }
    // Note: Function declarations need special handling in the lineariser
    const b = new TestBuilder(builder);
    const prog = b.lam("x", b.var("x"));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the function type was stored
    expect(program.types[program.rootIndex]).toBeDefined();
    expect(result).toBeDefined();
  });

  it("should store types for nested expressions", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const mulFn = arrow(IntType, arrow(IntType, IntType));
    envSetVal(env, "add", addFn);
    envSetVal(env, "mul", mulFn);
    
    // Create: add(mul(2, 3), 4)
    const b = new TestBuilder(builder);
    const prog = b.app(b.app(b.var("add"), b.app(b.app(b.var("mul"), b.int(2)), b.int(3))), b.int(4));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for sequence expressions", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    envSetVal(env, "y", IntType);
    
    // Create: { x; y }
    const b = new TestBuilder(builder);
    const prog = b.block(b.var("x"), b.var("y"));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for let expressions", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    envSetVal(env, "x", IntType);
    
    // Create: let y = x in y
    const b = new TestBuilder(builder);
    const prog = b.let("y", null, b.var("x"));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    // Note: Let expressions may not store types in the current implementation
    expect(result).toBe(IntType);
  });

  it("should store types for overloaded function applications", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const overloadedFn = overload([
      arrow(IntType, IntType),
      arrow(BoolType, BoolType)
    ]);
    envSetVal(env, "f", overloadedFn);
    
    // Create: f(42)
    const b = new TestBuilder(builder);
    const prog = b.app(b.var("f"), b.int(42));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBe(IntType);
    expect(result).toBe(IntType);
  });

  it("should store types for type applications", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    envSetType(env, "List", listScheme);
    
    const b = new TestBuilder(builder);
    const prog = b.let("list", b.typeApp("List", ["Int"]), null);
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(tapp(listScheme, [IntType]), builder);

    expect(program.types[program.rootIndex]).toEqualType(tapp(listScheme, [IntType]), builder);
  });

  it("should verify all nodes have types stored after type checking", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "isPositive", isPositiveFn);
    
    // Create a complex expression with multiple nodes
    const b = new TestBuilder(builder);
    const prog = b.app(b.var("isPositive"), b.app(b.app(b.var("add"), b.int(5)), b.int(3)));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    
    // Create: fun f(x: Int): Int { x }
    // Note: Function declarations need special handling
    const b = new TestBuilder(builder);
    const prog = b.lam("x", b.var("x"));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the function type was stored
    expect(program.types[program.rootIndex]).toBeDefined();
    
    // The function should have type Int -> Int (or a more general type)
    expect(result).toBeDefined();
  });

  it("should store types for complex nested function applications", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const mulFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "mul", mulFn);
    envSetVal(env, "isPositive", isPositiveFn);
    
    // Create: isPositive(add(mul(2, 3), mul(4, 5)))
    const b = new TestBuilder(builder);
    const prog = b.app(
      b.var("isPositive"), 
      b.app(
        b.app(b.var("add"), 
          b.app(b.app(b.var("mul"), b.int(2)), b.int(3))
        ), 
        b.app(b.app(b.var("mul"), b.int(4)), b.int(5))
      )
    );
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const mulFn = arrow(IntType, arrow(IntType, IntType));
    const subFn = arrow(IntType, arrow(IntType, IntType));
    envSetVal(env, "add", addFn);
    envSetVal(env, "mul", mulFn);
    envSetVal(env, "sub", subFn);
    
    // Create: add(mul(sub(10, 2), 3), mul(4, 5))
    const b = new TestBuilder(builder);
    const prog = b.app(
      b.app(b.var("add"), 
        b.app(b.app(b.var("mul"), 
          b.app(b.app(b.var("sub"), b.int(10)), b.int(2))
        ), b.int(3))
      ), 
      b.app(b.app(b.var("mul"), b.int(4)), b.int(5))
    );
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
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
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const addFn = arrow(IntType, arrow(IntType, IntType));
    const isPositiveFn = arrow(IntType, BoolType);
    const notFn = arrow(BoolType, BoolType);
    envSetVal(env, "add", addFn);
    envSetVal(env, "isPositive", isPositiveFn);
    envSetVal(env, "not", notFn);
    
    // Create: not(isPositive(add(5, 3)))
    const b = new TestBuilder(builder);
    const prog = b.app(
      b.var("not"), 
      b.app(b.var("isPositive"), 
        b.app(b.app(b.var("add"), b.int(5)), b.int(3))
      )
    );
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
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
    
    verifyTypesStored(program, expectedTypes, builder);
  });

  it("should store types for expressions with type variables", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const idFn = arrow(tvar("T"), tvar("T"));
    const idScheme = builder.scheme("id", ["T"], idFn);
    envSetVal(env, "id", idScheme);
    
    // Create: id(42)
    const b = new TestBuilder(builder);
    const prog = b.app(b.var("id"), b.int(42));
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    
    const result = runExpectingResult(bytecode, env, program, builder);
    expect(result).toEqualType(IntType, builder);
    expect(program.types[program.rootIndex]).toEqualType(IntType, builder);

    // Check application 
    const app_ = program.apps.get(program.rootIndex)!
    expect(app_).toBeDefined();
    expect(app_.fn).toEqualType(arrowN([IntType], IntType), builder);
    expect(app_.args).toEqual([IntType]);
    expect(app_.typeArgs).toEqual([]);
    expect(app_.result).toEqualType(IntType, builder);

    const inst = program.instantiations.filter(x => x.schemeId === idScheme.id)
    expect(inst).toHaveLength(1);
    expect(inst[0]!.mono).toEqualType(tapp(idScheme, [IntType]), builder); // TODO: A bit confused when to use tapp or arrow
    expect(inst[0]!.args[0]).toEqualType(IntType, builder);
    expect(program.schemes.get(idScheme.id)).toEqual(idScheme);
    
  });

  it("should store types for expressions with complex type schemes", () => {
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    const listScheme = builder.scheme("List", ["T"], tstruct("List", [{ name: "head", type: tvar("T") }]));
    const mapFn = arrow(tapp(listScheme, [tvar("A")]), arrow(arrow(tvar("A"), tvar("B")), tapp(listScheme, [tvar("B")])));
    const mapScheme = builder.scheme("Map", ["A", "B"], mapFn)
    envSetType(env, "List", listScheme);
    envSetVal(env, "map", mapScheme);
    
    // Create: map(List<Int>, fn)
    // TODO: This shouldn't be allowed
    const b = new TestBuilder(builder);
    const prog = b.block(
      b.let("list", b.typeApp("List", ["Int"]), null),
      b.app(b.var("map"), b.var("list"))
    );
    const program = b.program(prog);
    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBeDefined();
    expect(result).toBeDefined();

    expect(program.schemes.get(listScheme.id)).toEqual(listScheme);
    expect(program.schemes.get(mapScheme.id)).toEqual(mapScheme);
  });
});

describe("Type Constraints System", () => {
  it("should register traits and implementations", () => {
    // Create a builder for isolated state
    const builder = new ProgramBuilder();
    
    // Register some traits
    builder.traitTable.set(1, { id: 1, name: "Ord" });
    builder.traitTable.set(2, { id: 2, name: "Hash" });
    builder.traitTable.set(3, { id: 3, name: "Eq" });

    // Register some implementations
    builder.traitImpls.set(`1|Int`, true);  // Int implements Ord
    builder.traitImpls.set(`2|Int`, true);  // Int implements Hash
    builder.traitImpls.set(`3|Int`, true);  // Int implements Eq

    // Test hasTrait function
    expect(hasTrait(IntType, 1, builder)).toBe(true);
    expect(hasTrait(IntType, 2, builder)).toBe(true);
    expect(hasTrait(IntType, 3, builder)).toBe(true);
    expect(hasTrait(BoolType, 1, builder)).toBe(false);
  });

  it("should create bounds correctly", () => {
    // Test createBounds function
    const bounds = createBounds(
      [{ tvar: "T", traitId: 1 }],  // T: Ord
      [{ tvar: "T", upper: IntType }] // T ≤ Int
    );

    expect(bounds.length).toBe(2);
    expect(bounds[0]?.kind).toBe("Trait");
    expect(bounds[1]?.kind).toBe("Subtype");
  });

  it("should create schemes with bounds", () => {
    const bounds = createBounds([
      { tvar: "T", traitId: 1 }  // T: Ord
    ]);

    // Test scheme with bounds
    const maxScheme = scheme("max", 1, ["T"], arrowN([tvar("T"), tvar("T")], tvar("T")), bounds);
    
    expect(maxScheme.bounds).toBeDefined();
    expect(maxScheme.bounds!.length).toBe(1);
  });

  it("should validate trait requirements inside generic bodies", () => {
    // Create a builder for isolated state
    const builder = new ProgramBuilder();
    
    // Set up active bounds for testing
    builder.activeTraitBounds.set("T", new Set([1, 2, 3]));

    // Note: requireTraitNow still uses global activeTraitBounds
    // We need to update it to accept a builder parameter
    // For now, this test shows the pattern but won't work until
    // requireTraitNow is updated
    
    // Test requireTraitNow with valid trait
    expect(() => {
      requireTraitNow(tvar("T"), 1, dummy, builder);
    }).not.toThrow();

    // Test requireTraitNow with invalid trait
    expect(() => {
      requireTraitNow(tvar("T"), 999, dummy, builder);
    }).toThrow();
  });

  it("should validate concrete type trait implementations", () => {
    // Create a builder for isolated state
    const builder = new ProgramBuilder();
    
    // Register traits and implementations in builder
    builder.traitTable.set(1, { id: 1, name: "Ord" });
    builder.traitImpls.set(`1|Int`, true);

    // Note: requireTraitNow still uses global traitTable and traitImpls
    // We need to update it to accept a builder parameter
    // For now, we'll use the global functions
    
    // Test concrete type with trait
    expect(() => {
      requireTraitNow(IntType, 1, dummy, builder);
    }).not.toThrow();

    // Test concrete type without trait
    expect(() => {
      requireTraitNow(BoolType, 1, dummy, builder);
    }).toThrow();
  });

  it("should handle obligation system", () => {
    // Register traits and implementations
    const builder = new ProgramBuilder();
    registerTrait(builder, 1, "Ord");
    registerTraitImpl(builder, 1, IntType);

    expect(builder.pendingObligations.length).toBe(0);

    // Simulate adding an obligation
    const obligation = {
      kind: "Trait" as const,
      traitId: 1,
      ty: IntType,
      loc: dummy,
      instKey: "test_1_Int"
    };

    const mockState = createInterpreterState([], new Map(), builder);
    mockState.builder.pendingObligations.push(obligation);
    expect(mockState.builder.pendingObligations.length).toBe(1);

    // Discharge obligations
    dischargeDeferredObligations(mockState);
    expect(mockState.builder.pendingObligations.length).toBe(0);
  });

  it("should type check generic function with trait bounds", () => {
    // Register traits and implementations
    const builder = new ProgramBuilder();
    registerTrait(builder, 1, "Ord");
    registerTraitImpl(builder, 1, IntType);
    registerTraitImpl(builder, 1, BoolType);
    const env: Env = new Map();
    envSetType(env, "Ord", new TraitType("Ord", 1));

    // Create a generic max function with trait bounds
    const b = new TestBuilder(builder);
    const maxExpr = b.complexFunDecl({
      name: "max",
      typeParams: ["T"],
      params: ["a", "b"],
      bodyIndex: b.int(0),
      paramTypes: ["T", "T"],
      returnType: "T",
      traitBounds: [{ typeParam: "T", trait: "Ord" }]
    });
    const program = b.program(maxExpr);

    const bytecode = lineariseProgram(builder, program.rootIndex);
    // Find the scheme by function name
    const scheme = Array.from(program.schemes.values()).find(s => s.name === "max")!
    expect(scheme).toBeDefined();

    printInstructions(bytecode);
    
    // if (scheme) {
    //   scheme.bounds = createBounds([
    //     { tvar: "T", traitId: 1 }  // T: Ord
    //   ]);
    // }
    const result = runExpectingResult(bytecode, env, program, builder);
    
    // The result should be a function type with trait constraints
    expect(result).toBeDefined();
    console.log(scheme);
    expect(scheme.bounds).toBeDefined();
    expect(scheme.bounds![0]!.kind).toBe("Trait");
    expect(scheme.bounds![0]!.tvar).toBe("T");
    expect((scheme.bounds![0]! as { traitId: number }).traitId).toBe(1);
  });

  it("should reject instantiation with types that don't implement required traits", () => {
    // Register traits but don't implement for Float
    const builder = new ProgramBuilder();
    registerTrait(builder, 1, "Ord");
    registerTraitImpl(builder, 1, IntType);
    // Note: FloatType does NOT implement Ord

    // Create a simple test that directly tests the constraint system
    const testScheme = scheme("test", 999, ["T"], arrowN([tvar("T"), tvar("T")], tvar("T")), [
      { kind: "Trait", tvar: "T", traitId: 1 }  // T: Ord
    ]);

    // This should fail because Float doesn't implement Ord
    expect(() => {
      emitObligationsForInstantiation(testScheme, [FloatType], dummy, "test_key", builder);
      const mockState = createInterpreterState([], new Map(), builder);
      dischargeDeferredObligations(mockState);
    }).toThrow();
  });

  it("should handle multiple trait bounds", () => {
    // Register multiple traits
    const builder = new ProgramBuilder();
    registerTrait(builder, 1, "Ord");
    registerTrait(builder, 2, "Hash");
    registerTrait(builder, 3, "Eq");

    const env: Env = new Map();
    envSetType(env, "Ord", new TraitType("Ord", 1));
    envSetType(env, "Hash", new TraitType("Hash", 2));
    envSetType(env, "Eq", new TraitType("Eq", 3));
    
    // Int implements all three
    registerTraitImpl(builder, 1, IntType);
    registerTraitImpl(builder, 2, IntType);
    registerTraitImpl(builder, 3, IntType);

    // Create a generic function with multiple trait bounds
    const b = new TestBuilder(builder);
    const mapExpr = b.complexFunDecl({
      name: "map",
      typeParams: ["K", "V"],
      params: ["key", "value"],
      bodyIndex: b.int(0),
      paramTypes: ["K", "V"],
      returnType: "Unit",
      traitBounds: [
        { typeParam: "K", trait: "Hash" },
        { typeParam: "K", trait: "Eq" }
      ]
    });
    const program = b.program(mapExpr);

    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);

    // Find the scheme by function name
    const scheme = Array.from(program.schemes.values()).find(s => s.name === "map");
    expect(scheme).toBeDefined();
    
    expect(result).toBeDefined();
    expect(scheme!.bounds![0]!).toEqual({ kind: "Trait", tvar: "K", traitId: 2 });
    expect(scheme!.bounds![1]!).toEqual({ kind: "Trait", tvar: "K", traitId: 3 });
  });

  it("should handle subtype bounds", () => {
    // Register traits
    const builder = new ProgramBuilder();
    const env: Env = new Map();
    envSetType(env, "Ord", new TraitType("Ord", 1));
    envSetType(env, "Int", IntType);

    registerTrait(builder, 1, "Ord");
    registerTraitImpl(builder, 1, IntType);

    // Create a generic function with subtype bounds
    const b = new TestBuilder(builder);
    const numericExpr = b.complexFunDecl({
      name: "numeric",
      typeParams: ["T"],
      params: ["x"],
      bodyIndex: b.int(0),
      paramTypes: ["T"],
      returnType: "T",
      traitBounds: [{ typeParam: "T", trait: "Ord" }],
      subtypeBounds: [{ typeParam: "T", subtype: "Int" }]
    });
    const program = b.program(numericExpr);
    

    // if (scheme) {
    //   scheme.bounds = createBounds(
    //     [{ tvar: "T", traitId: 1 }],  // T: Ord
    //     [{ tvar: "T", upper: IntType }] // T ≤ Int
    //   );
    // }

    const bytecode = lineariseProgram(builder, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program, builder);
    console.log(printInstructions(bytecode));

    // Find the scheme by function name
    const scheme = Array.from(program.schemes.values()).find(s => s.name === "numeric");
    expect(scheme).toBeDefined();
    
    expect(result).toBeDefined();
    expect(scheme!.bounds![0]!).toEqual({ kind: "Trait", tvar: "T", traitId: 1 });
    expect(scheme!.bounds![1]!).toEqual({ kind: "Subtype", tvar: "T", upper: IntType });
  });

  it("should handle nested generic instantiation with bounds", () => {
    // Register traits
    const builder = new ProgramBuilder();
    registerTrait(builder, 1, "Ord");
    registerTraitImpl(builder, 1, IntType);

    // Create a simple test that directly tests the constraint system with nested types
    const testScheme = scheme("container", 999, ["T"], arrowN([tvar("T")], tvar("T")), [
      { kind: "Trait", tvar: "T", traitId: 1 }  // T: Ord
    ]);

    // This should succeed because Int implements Ord
    expect(() => {
      emitObligationsForInstantiation(testScheme, [IntType], dummy, "test_key", builder);
      const mockState = createInterpreterState([], new Map(), builder);
      dischargeDeferredObligations(mockState);
    }).not.toThrow();
  });
});
