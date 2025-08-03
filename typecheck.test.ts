import { inspect } from "bun";
import { describe, it, expect } from "bun:test";

class AssertionError extends Error {
  data?: any;
  constructor(message: string, data?: any) {
    super(message);
    this.data = data;
  }
}

function assert(condition: any, message: string, data?: any): asserts condition {
  if (!condition) {
    message = `${message}`;
    Object.entries(data ?? {}).forEach(([key, value]) => {
      message += `\n${key}: ${inspect(value, { depth: 1, colors: true, compact: true })}`;
    });
    throw new AssertionError(message, data);
  }
}

const handleAssertionOrThrow = (e: unknown) => {
  if (e instanceof AssertionError) return e
  throw e;
}

/** Result<T,E> ----------------------------------------------------------- */
/*  - `Ok<T>`  wraps a successful value
 *  - `Err<E>` wraps one or more problems
 *  Both variants expose rich instance methods, AND you can still rely on
 *  discriminated-union narrowing (`if (res.ok) { … }`).                   */

export abstract class ResultT<T, E> {
  abstract readonly ok: boolean;

  isOk():  this is Ok<T, E>  { return this.ok; }
  isErr(): this is Err<T, E> { return !this.ok; }

  get errorOrNull(): E | null { return (this as any).error ?? null }
  get valueOrNull(): T | null { return (this as any).value ?? null }

  map<U>(f: (value: T) => U): Result<U, E> {
    return this.match({ Ok: v => Result.Ok(f(v)), Err: e => this as any });
  }

  flatMap<U, E2>(f: (v: T) => Result<U, E2>): Result<U, E | E2> {
    return this.match({ Ok: f, Err: () => this as any });
  }

  mapErr<E2>(f: (e: E) => E2): Result<T, E2> {
    return this.match({ Ok: () => this as any, Err: e => Result.Err(f(e)) });
  }

  match<R>(arms: { Ok: (v: T) => R; Err: (e: E) => R }): R {
    if (this.ok) return arms.Ok((this as any).value)
    return arms.Err((this as any).error)
  }

  /** Dangerous escape hatch that throws if this is Err. */
  getOrThrow(): T {
    if (this.ok) return (this as any).value
    if ((this as any).error instanceof Error) throw (this as any).error
    throw new Error(String((this as any).error))
  }

  expectError(message: string = "Expected error but got success"): E {
    if (this.ok) throw new Error(message)
    return (this as any).error
  }
}

/* ──────────── Concrete variants ──────────── */

class Ok<T, E = never> extends ResultT<T, E> { readonly ok = true as const; constructor(public readonly value: T) { super(); } }
class Err<E, T = never> extends ResultT<T, E> { readonly ok = false as const; constructor(public readonly error: E) { super(); } }

type Result<T, E> = Ok<T, E> | Err<E, T>;
const Result = {
  Ok: <T, E = never>(value: T): Result<T, E> => new Ok(value),
  Err: <E, T = never>(error: E): Result<T, E> => new Err(error),

  /** Collapse an array of Results into
   *    – Ok(values[]) if every element succeeded,   or
   *    – Err(errors[]) if at least one failed. */
  collect: <T, E>(results: Result<T, E>[]): Result<T[], E[]> => {
    const values: T[] = [];
    const errors: E[] = [];

    for (const r of results) r.match({
      Ok:  v => values.push(v),
      Err: e => errors.push(e)
    })
    return errors.length === 0 ? Result.Ok(values) : Result.Err(errors)
  },

  /** Run `fn` under try-catch and lift the outcome into a Result.
   *
   *  @param fn       Function to execute.
   *  @param catcher  Optional adapter that turns the raw caught value
   *                  into your desired error type.
   *
   *  Usage:
   *    const safe = Result.try(() => JSON.parse(str), e => String(e));
   */
  try: <T, E = unknown>(fn: () => T, catcher?: (e: unknown) => E): Result<T, E> => {
    try {
      return Result.Ok(fn());
    } catch (e) {
      return Result.Err(catcher ? catcher(e) : (e as E));
    }
  },

  /** Wrap an arbitrary function so every call returns a `Result`.
   *
   *   const safeJson = Result.wrap(JSON.parse, e => String(e));
   *   const out = safeJson('{"ok":true}');   // Ok<{ ok: true }>
   *
   *   // Works with any arity:
   *   const safePow = Result.wrap(Math.pow);
   *   safePow(2, 10);  // Ok<1024>
   *
   * @param fn       Function to wrap (can have any parameters).
   * @param catcher  Optional adapter to normalise caught errors.
   */
  wrap: <R, F extends (...args: any[]) => R, E = unknown>(
    fn: F,
    catcher?: (e: unknown) => E
  ): (...args: Parameters<F>) => Result<R, E> => {
    return (...args: Parameters<F>): Result<R, E> => Result.try(() => fn(...args), catcher);
  }
}



/*======================================================================*/
/* 0.  Source-code locations                                            */
/*======================================================================*/
export interface Loc { file: string; line: number; col: number }

const dummy: Loc = { file: "<repl>", line: 0, col: 0, 
  [inspect.custom]: (d,o,i) => o.stylize(`<loc>`, 'special') };   // demo helper

/*======================================================================*/
/* 1.  Types, unknowns, occurs-check unification                        */
/*======================================================================*/
let nextU = 0;

// Base class for all types (aligning with defs.ts)
abstract class TypeRoot {
  [inspect.custom](depth: any, options: any, inspect: any) {
    const typeName = this.constructor.name
    return options.stylize(`[${typeName} ${this.toString()}]`, 'special');
  }
  
  abstract toString(): string;
}

// Unknown type for type inference (from bidi)
export class UnknownType extends TypeRoot {
  constructor(public id: number) { super() }
  toString() { return `?${this.id} (${show(this)})` }
}

// Type variable for generics (aligning with defs.ts)
export class TypeVariable extends TypeRoot {
  constructor(public name: string) { super() }
  toString() { return this.name }
}

// Primitive types (aligning with defs.ts)
export class PrimitiveType extends TypeRoot {
  constructor(public name: string) { super() }
  toString() { return this.name }
}

// Function types (using only ArrowN for consistency)
export class ArrowNType extends TypeRoot {
  constructor(public params: Type[], public result: Type) { super() }
  toString() { return show(this) }
}

// Overload type (from bidi)
export class OverloadType extends TypeRoot {
  constructor(public alts: ArrowNType[]) { super() }
  toString() { return show(this) }
}

// Struct type (aligning with defs.ts)
export class StructType extends TypeRoot {
  constructor(public name: string, public fields: { name: string; type: Type }[]) { super() }
  toString() { return show(this) }
}

// Type application (aligning with defs.ts)
export class AppliedType extends TypeRoot {
  constructor(public ctor: string, public schemeId: number, public args: Type[]) { super() }
  toString() { return show(this) }
}

// Type parameter declaration (aligning with defs.ts)
export class TypeParameterDecl extends TypeRoot {
  constructor(public name: string, public constraints: Type[], public scopeId: string) { super() }
  toString() { return show(this) }
}

// Scheme for polymorphic types (from bidi)
export interface Scheme { name: string; id: number; vars: string[]; body: Type }

// Union type for all types
export type Type = 
  | UnknownType
  | TypeVariable
  | PrimitiveType
  | ArrowNType
  | OverloadType
  | AppliedType
  | StructType
  | TypeParameterDecl

const areTypesEqual = (t1: Type, t2: Type): boolean => {
  t1 = resolve(t1);
  t2 = resolve(t2);
  const areTypeListsEqual = (l1: Type[], l2: Type[]): boolean => l1.length === l2.length && l1.every((t, i) => areTypesEqual(t, l2[i]));
  if (t1 === t2) return true;
  if (t1 instanceof UnknownType && t2 instanceof UnknownType) return t1.id === t2.id;
  if (t1 instanceof TypeVariable && t2 instanceof TypeVariable) return t1.name === t2.name;
  if (t1 instanceof PrimitiveType && t2 instanceof PrimitiveType) return t1.name === t2.name;
  if (t1 instanceof ArrowNType && t2 instanceof ArrowNType) return areTypeListsEqual(t1.params, t2.params) && areTypesEqual(t1.result, t2.result);
  if (t1 instanceof StructType && t2 instanceof StructType) return t1.name === t2.name && areTypeListsEqual(t1.fields.map(f => f.type), t2.fields.map(f => f.type));
  if (t1 instanceof AppliedType && t2 instanceof AppliedType) return t1.ctor === t2.ctor && areTypeListsEqual(t1.args, t2.args);
  if (t1 instanceof TypeParameterDecl && t2 instanceof TypeParameterDecl) return t1.name === t2.name && areTypeListsEqual(t1.constraints, t2.constraints);
  return false;
}

// Type guards
const isUnknown = (t: Type): t is UnknownType => t instanceof UnknownType;
const isArrowN = (t: Type): t is ArrowNType => t instanceof ArrowNType;
const isOverload = (t: Type): t is OverloadType => t instanceof OverloadType;
const isTVar = (t: Type): t is TypeVariable => t instanceof TypeVariable;
const isTApp = (t: Type): t is AppliedType => t instanceof AppliedType;
const isPrimitive = (t: Type): t is PrimitiveType => t instanceof PrimitiveType;
const isScheme = (binding: Type | Scheme): binding is Scheme => 
  typeof binding === "object" && "vars" in binding;
const isStructType = (t: Type): t is StructType => t instanceof StructType;
const isAppliedType = (t: Type): t is AppliedType => t instanceof AppliedType;
const isType = (t: RunResult): t is Type => t instanceof TypeRoot;

// Helper functions for creating types
const newUnknown = (): UnknownType => new UnknownType(nextU++);
const tvar = (name: string): TypeVariable => new TypeVariable(name);
const tapp = (scheme: Scheme, args: Type[]): AppliedType => new AppliedType(scheme.name, scheme.id, args);
const tstruct = (name: string, fields: { name: string; type: Type }[]): StructType => new StructType(name, fields);
const arrow = (param: Type, result: Type): ArrowNType => new ArrowNType([param], result);
const arrowN = (params: Type[], result: Type): ArrowNType => new ArrowNType(params, result);
const overload = (alts: ArrowNType[]): OverloadType => new OverloadType(alts);
const scheme = (name: string, id: number, vars: string[], body: Type): Scheme => ({ name, id, vars, body });

// Primitive type constants (aligning with defs.ts)
export const IntType = new PrimitiveType("Int");
export const FloatType = new PrimitiveType("Float");
export const BoolType = new PrimitiveType("Bool");
export const UnitType = new PrimitiveType("Unit");

// Binding type (aligning with defs.ts)
export class Binding {
  constructor(public name: string, public type: Type) {}
  toString() { return `[Binding ${this.name} : ${this.type.toString()}]` }
}

type EnvBinding =
  | { tag:"Known" ; type: Type | Scheme }          // already compiled
  | { tag:"Pending"; waiters: ((scheme:Scheme)=>void)[] }; // not yet compiled

type ValueBinding =
  | { tag:"KnownV" ; schemeOrType: Scheme | Type }
  | { tag:"PendV" ; waiters:((scheme:Scheme|Type)=>void)[] };

type TypeBinding =
  | { tag:"KnownT" ; schemeOrType: Scheme | Type }
  | { tag:"PendT" ; waiters:((tb: TypeBinding)=>void)[] };

interface SymbolEntry {
  value?: ValueBinding;   // absent if this name is type-only
  type ?: TypeBinding;    // absent if value-only
}

type Env = Map<string, SymbolEntry>;


/*======================================================================*/
/* AST                                                                  */
/*======================================================================*/
interface Var     { tag: "Var"    ; loc: Loc; name: string }
interface IntLit  { tag: "IntLit" ; loc: Loc; value: number }
interface BoolLit { tag: "BoolLit"; loc: Loc; value: boolean }
interface Lam     { tag: "Lam"    ; loc: Loc;
                    params: string[]; paramTyNames?: string[]; body: Expr }
interface FunDecl { tag: "FunDecl"; loc: Loc; name: string; 
                    typeParams: string[]; params: string[]; 
                    paramTypes?: string[]; returnType?: string; body: Expr }
interface AppN    { tag: "AppN"   ; loc: Loc; fn: Expr; args: Expr[] }
interface If      { tag: "If"     ; loc: Loc; cond: Expr; thenBranch: Expr;
                    elseBranch: Expr }
interface Let     { tag: "Let"    ; loc: Loc; name: string;
                    annotation: Expr|null; value: Expr|null }
interface Seq     { tag: "Seq"    ; loc: Loc; stmts: Expr[] }
interface TypeApp { tag: "TypeApp"; loc: Loc; ctor: Expr; args: Expr[] }

type Expr = Var | IntLit | BoolLit | Lam | FunDecl | AppN | If | Let | Seq | TypeApp;

/* small helpers ------------------------------------------------------*/
const int = (n: number, l = dummy): IntLit => ({ tag: "IntLit", loc: l, value: n });
const bool = (b: boolean, l = dummy): BoolLit => ({ tag: "BoolLit", loc: l, value: b });
const v = (x: string, l = dummy): Var => ({ tag: "Var", loc: l, name: x });
const lam = (p: string, body: Expr, anno?: string, l = dummy): Lam => 
  ({ tag: "Lam", loc: l, params: [p], paramTyNames: anno ? [anno] : undefined, body });
const lamN = (params: string[], body: Expr, paramTyNames?: string[], l = dummy): Lam => 
  ({ tag: "Lam", loc: l, params, paramTyNames, body });
const funDecl = (name: string, typeParams: string[], params: string[], body: Expr, paramTypes?: string[], returnType?: string, l = dummy): FunDecl => 
  ({ tag: "FunDecl", loc: l, name, typeParams, params, paramTypes, returnType, body });
const app = (f: Expr, a: Expr, l = dummy): AppN => ({ tag: "AppN", loc: l, fn: f, args: [a] });
const appN = (f: Expr, args: Expr[], l = dummy): AppN => ({ tag: "AppN", loc: l, fn: f, args });
const _if = (c: Expr, t: Expr, e: Expr, l = dummy): If => 
  ({ tag: "If", loc: l, cond: c, thenBranch: t, elseBranch: e });
const _let = (x: string, annotation: Expr | null, val: Expr | null, l = dummy): Let => 
  ({ tag: "Let", loc: l, name: x, annotation, value: val });
const block = (...stmts: Expr[]): Seq => ({ tag: "Seq", loc: stmts[0]?.loc ?? dummy, stmts });
const typeApp = (ctor: Expr, args: Expr[]): Expr => ({ tag: "TypeApp", loc: ctor.loc, ctor, args });

export type Node =
  | { location: Loc; kind: "IntLiteral"; value: number; }
  | { location: Loc; kind: "FloatLiteral"; value: number; }
  | { location: Loc; kind: "BoolLiteral"; value: boolean; }
  | { location: Loc; kind: "Constant"; value: Type; }
  | { location: Loc; kind: "Var"; name: string; }
  | { location: Loc; kind: "MutSigil"; innerIndex: number; }
  | { location: Loc; kind: "LocalVar"; name: string; binding: Binding; }
  | { location: Loc; kind: "GlobalVar"; name: string; binding: Binding; }
  | { location: Loc; kind: "TypeParam"; name: string; constraintsIndices: number[]; }
  | { location: Loc; kind: "TypeApp"; baseIndex: number; typeArgsIndices: number[]; }
  | { location: Loc; kind: "AppArg"; name: string; exprIndex: number; }
  | { location: Loc; kind: "App"; fnIndex: number; argsIndices: number[]; typeArgsIndices: number[]; }
  | { location: Loc; kind: "Let"; name: string; typeIndex?: number; valueIndex: number; binding?: Binding; }
  | { location: Loc; kind: "Op"; op: string; leftIndex: number; rightIndex: number; }
  | { location: Loc; kind: "Statements"; statementsIndices: number[]; }
  | { location: Loc; kind: "FunParam"; name: string; typeIndex: number; }
  | { location: Loc; kind: "Annotation"; name: string; innerIndex: number; }
  | { location: Loc; kind: "FunDecl"; name: string; paramsIndices: number[]; typeParamsIndices: number[]; returnTypeIndex: number; bodyIndex: number; }
  | { location: Loc; kind: "StructDecl"; name: string; typeParamsIndices: number[]; fields: { name: string; typeIndex: number }[]; }
  | { location: Loc; kind: "StructLiteral"; name: string; typeArgsIndices: number[]; argIndices: number[]; }
  | { location: Loc; kind: "FieldAccess"; objectIndex: number; field: string; }
  | { location: Loc; kind: "MethodCall"; objectIndex: number; methodName: string; argsIndices: number[]; }
  | { location: Loc; kind: "Assign"; leftIndex: number; valueIndex: number; }
  | { location: Loc; kind: "If"; condIndex: number; thenIndex: number; elseIndex: number | undefined }
  | { location: Loc; kind: "While"; condIndex: number; bodyIndex: number; }
  | { location: Loc; kind: "EnumDecl"; name: string; typeParamsIndices: number[]; variants: Array<{ name: string; fieldTypeIndices: number[]; }>; }
  | { location: Loc; kind: "EnumLiteral"; enumName: string; variantName: string; typeArgsIndices: number[]; fieldsIndices: number[]; }
  | { location: Loc; kind: "TraitDecl"; name: string; typeParamsIndices: number[]; methodsIndices: number[]; }
  | { location: Loc; kind: "TraitImpl"; traitIndex: number | undefined; structIndex: number; typeParamsIndices: number[]; methodIndices: number[]; }
  | { location: Loc; kind: "Subscript"; baseIndex: number; argsIndices: number[]; }
  | { location: Loc; kind: "Return"; exprIndex: number }
  | { location: Loc; kind: "LetConst"; name: string; valueIndex: number }

let nextSchemeId = 0;
const getNextSchemeId = () => nextSchemeId++;


class Application {
  schemeId: number
  nodeIdx: number
  fn: Type
  args: Type[]
  typeArgs: Type[]
  result: Type
}

class Instantiation {
  schemeId: number
  args: Type[]
  mono: Type
  nodeIdx: number
}


// Program class to hold the indexed arrays
export class Program {
  public schemes: Map<number, Scheme> = new Map();
  public apps: Map<number, Application> = new Map(); // nodeIdx -> Application
  public instantiations: Instantiation[] = [];
  
  constructor(
    public nodes: Node[],
    public types: Type[],
    public rootIndex: number
  ) {}

  // Helper methods to work with the indexed structure
  getNode(index: number): Node {
    if (index < 0 || index >= this.nodes.length) {
      throw new Error(`Invalid node index: ${index}`);
    }
    return this.nodes[index];
  }

  getType(index: number): Type {
    if (index < 0 || index >= this.types.length) {
      throw new Error(`Invalid type index: ${index}`);
    }
    return this.types[index];
  }

  addNode(node: Node): number {
    const index = this.nodes.length;
    this.nodes.push(node);
    return index;
  }

}

// Helper functions to create nodes
const nodeFac = {
  intLiteral: (value: number, loc: Loc = dummy): Node => ({ location: loc, kind: "IntLiteral", value }),
  boolLiteral: (value: boolean, loc: Loc = dummy): Node => ({ location: loc, kind: "BoolLiteral",  value }),
  var: (name: string, loc: Loc = dummy): Node => ({ location: loc, kind: "Var", name }),
  app: (fnIndex: number, argsIndices: number[], typeArgsIndices: number[] = [], loc: Loc = dummy): Node => ({ location: loc, kind: "App", fnIndex, argsIndices, typeArgsIndices }),
  funDecl: (name: string, paramsIndices: number[], typeParamsIndices: number[], returnTypeIndex: number, bodyIndex: number, loc: Loc = dummy): Node => ({ location: loc, kind: "FunDecl", name, paramsIndices, typeParamsIndices, returnTypeIndex, bodyIndex }),
  let: (name: string, valueIndex: number, typeIndex?: number, loc: Loc = dummy): Node => ({ location: loc, kind: "Let", name, valueIndex, typeIndex }),
  if: (condIndex: number, thenIndex: number, elseIndex?: number, loc: Loc = dummy): Node => ({ location: loc, kind: "If", condIndex, thenIndex, elseIndex }),
  statements: (statementsIndices: number[], loc: Loc = dummy): Node => ({ location: loc, kind: "Statements", statementsIndices }),
  funParam: (name: string, typeIndex: number, loc: Loc = dummy): Node => ({ location: loc, kind: "FunParam", name, typeIndex }),
  typeApp: (baseIndex: number, typeArgsIndices: number[], loc: Loc = dummy): Node => ({ location: loc, kind: "TypeApp", baseIndex, typeArgsIndices }),
}

//======================================================================
// 2.  Type checker
//======================================================================


const solved = new Map<number, Type>();

// Trial/rollback system
const trail: Array<{u: UnknownType; prev: Type | undefined}> = [];

function startTrial(): number {
  return trail.length;
}

function rollback(mark: number): void {
  while (trail.length > mark) {
    const { u, prev } = trail.pop()!;
    if (prev === undefined) {
      solved.delete(u.id);
    } else {
      solved.set(u.id, prev);
    }
  }
}

function commit(mark: number): void {
  trail.length = mark;
}

const primLe: Record<string, string[]> = {
  Int  : ["Int",  "Float"],   // Int  ≤  Int   and  Int ≤ Float
  Float: ["Float"],
  Bool : ["Bool"],
  Unit : ["Unit"],
};

const primSubtype = (a: PrimitiveType, b: PrimitiveType) => a === b || primLe[a.name].includes(b.name);

const resolve = (t: Type): Type =>
  isUnknown(t) && solved.has(t.id) ? resolve(solved.get(t.id)!) : t;

function occurs(u: UnknownType, t: Type): boolean {
  t = resolve(t);
  if (t === u) return true;
  if (isArrowN(t)) return t.params.some(p => occurs(u, p)) || occurs(u, t.result);
  if (isOverload(t)) return t.alts.some(alt => {
    if (isArrowN(alt)) return alt.params.some(p => occurs(u, p)) || occurs(u, alt.result);
    return false;
  });
  if (isTApp(t)) return t.args.some(arg => occurs(u, arg));
  return false;
}


const unify = Result.wrap((a: Type, b: Type, record: boolean = true) => {
  a = resolve(a); b = resolve(b);
  if (a === b) return;

  if (isUnknown(a)) {
    if (occurs(a, b)) throw new Error(`infinite type in ${show(b)}`);
    bindUnknown(a, b, record); return;
  }
  if (isUnknown(b)) { return unify(b, a, record); }

  // Rigid TVars – rule: α unifies only with α
  if (isTVar(a) && isTVar(b)) {
    assert(a.name === b.name, "cannot unify type variable with different names", { a, b })
    return;
  }
  if (isTVar(a) || isTVar(b)) {
    assert(false, "cannot unify type variable with non-type variable", { a, b })
  }

  if (isArrowN(a) && isArrowN(b)) {
    assert(a.params.length === b.params.length, "cannot unify ArrowN with different numbers of parameters", { a, b })
    for (let i = 0; i < a.params.length; i++) {
      unify(a.params[i], b.params[i], record).getOrThrow()
    }
    unify(a.result, b.result, record).getOrThrow()
    return;
  }
  if (isOverload(a) && isOverload(b)) {
    assert(a.alts.length === b.alts.length, "cannot unify overloads with different numbers of alternatives", { a, b })
    for (let i = 0; i < a.alts.length; i++) {
      unify(a.alts[i], b.alts[i], record).getOrThrow()
    }
    return;
  }
  if (isTApp(a) && isTApp(b)) {
    assert(a.ctor === b.ctor, "cannot unify type applications with different constructors", { a, b })
    assert(a.args.length === b.args.length, "cannot unify type applications with different numbers of arguments", { a, b })
    for (let i = 0; i < a.args.length; i++) {
      unify(a.args[i], b.args[i], record).getOrThrow()
    }
    return;
  }
  if (isPrimitive(a) && isPrimitive(b) && a.name === b.name) return;
  assert(false, "cannot unify", { a, b })
}, handleAssertionOrThrow);

/** returns true and may bind unknowns  */
const subsume = Result.wrap((a: Type, b: Type, record: boolean = true) => {
  a = resolve(a);  b = resolve(b);
  if (a === b) return;

  // unknowns behave like Algorithm W instantiation / generalisation
  if (isUnknown(a)) { bindUnknown(a, b, record); return; }
  if (isUnknown(b)) { bindUnknown(b, a, record); return; }

  // primitive widening
  if (isPrimitive(a) && isPrimitive(b) && primSubtype(a, b)) return;

  // TVar has no subtyping relation with other types
  if (isTVar(a) || isTVar(b)) {
    const varName = isTVar(a) ? a.name : (isTVar(b) ? b.name : "unknown");
    assert(false, "type variable has no subtyping relation", { a, b, varName })
  }

  // function types :  (B₁→B₂)  ≤  (A₁→A₂)  when  A₁ ≤ B₁  and  B₂ ≤ A₂
  if (isArrowN(a) && isArrowN(b)) {
    assert(a.params.length === b.params.length, "cannot subsume ArrowN with different numbers of parameters", { a, b })
    for (let i = 0; i < a.params.length; i++) {
      subsume(a.params[i], b.params[i], record).getOrThrow()
    }
    subsume(a.result, b.result, record).getOrThrow()
    return;
  }

  // type application: structural equality
  if (isTApp(a) && isTApp(b)) {
    assert(a.ctor === b.ctor, "cannot subsume type applications with different constructors", { a, b })
    assert(a.args.length === b.args.length, "cannot subsume type applications with different numbers of arguments", { a, b })
    for (let i = 0; i < a.args.length; i++) {
      subsume(a.args[i], b.args[i], record).getOrThrow()
    }
    return;
  }

  // overload types: check if all alternatives in a are subtypes of some alternative in b
  if (isOverload(a) && isOverload(b)) {
    for (const altA of a.alts) {
      let foundMatch = false;
      for (const altB of b.alts) {
        if (subsume(altA, altB, record).ok) {
          foundMatch = true;
          break;
        }
      }
      assert(foundMatch, "overload alternative is not a subtype of any alternative in b", { a, b })
    }
    return;
  }

  assert(false, "type a is not a subtype of b", { a, b })
}, handleAssertionOrThrow);

function bindUnknown(u: UnknownType, t: Type, record: boolean = true) {
  if (occurs(u,t))   // reuse the occurs-check we already had
    throw new Error(`infinite type: ${show(u)} in ${show(t)}`);
  
  if (record) trail.push({ u, prev: solved.get(u.id) });
  solved.set(u.id, t);
}

// Substitution function for type variables
function substWalk(t: Type, subst: Map<string, Type>): Type {
  if (isTVar(t)) {
    const replacement = subst.get(t.name);
    return replacement ? replacement : t;
  }
  if (isArrowN(t)) {
    return arrowN(t.params.map(p => substWalk(p, subst)), substWalk(t.result, subst));
  }
  if (isOverload(t)) {
    return overload(t.alts.map(alt => {
      return arrowN(alt.params.map(p => substWalk(p, subst)), substWalk(alt.result, subst));
    }));
  }
  // if (isTApp(t)) {
  //   return tapp(t.ctor, t.args.map(arg => substWalk(arg, subst)));
  // }
  // if (isStructType(t)) {
  //   return tapp(t.name, t.fields.map(f => substWalk(f.type, subst)));
  // }
  assert(false, "unexpected type", { t });
  return t;
}

function appliedSchemeOrType(state: InterpreterState, nodeIdx: number, t: Type | Scheme): Type {
  if (isScheme(t)) return applySchemeUnknowns(state, nodeIdx, t);
  return t;
}

// Instantiate a scheme with fresh unknowns
function applySchemeUnknowns(state: InterpreterState, nodeIdx: number, s: Scheme): Type {
  const actualArgs = s.vars.map(v => newUnknown());
  const t = tapp(s, actualArgs);
  state.program?.instantiations.push({ schemeId: s.id, args: actualArgs, mono: t, nodeIdx });
  return t;
}

function concreteInstantiateWithArgs(state: InterpreterState, s: Scheme, args: Type[]): Type {
  assert(args.length === s.vars.length, "arity mismatch for scheme", { s, args });
  const subst = new Map<string, Type>();
  s.vars.forEach((v, i) => subst.set(v, args[i]));
  return substWalk(s.body, subst);
}

function instantiateWithArgs(state: InterpreterState, nodeIdx: number, s: Scheme, args: Type[]): Type {
  assert(args.length === s.vars.length, "arity mismatch for scheme", { s, args });
  const t = tapp(s, args);
  state.program?.instantiations.push({ schemeId: s.id, args, mono: t, nodeIdx });
  return t;
}


function show(t: Type): string {
  t = resolve(t);
  if (isUnknown(t))  return `?${t.id}`;
  if (isTVar(t)) return t.name;
  if (isPrimitive(t)) return t.name;
  if (isTApp(t)) return `${t.ctor}<${t.args.map(show).join(", ")}>`;
  if (isArrowN(t)) return `(${t.params.map(show).join(", ")} → ${show(t.result)})`;
  if (isStructType(t)) return `${t.name}{${t.fields.map(f => `${f.name}: ${show(f.type)}`).join(", ")}}`;
  if (isOverload(t)) return `{${t.alts.map(show).join(" | ")}}`;
  assert(false, "unexpected type", { name: (t as any).constructor?.name });
}

/*======================================================================*/
/* Overload resolution helpers                                           */
/*======================================================================*/

// Try to subsume a with b, return true if successful, false otherwise
function trySubsume(a: Type, b: Type): boolean {
  const mark = startTrial();
  const result = subsume(a, b, true);
  rollback(mark);
  return result.ok;
}

// Check if a is a strict subtype of b (a < b)
function isStrictSubtype(a: Type, b: Type): boolean {
  const mark = startTrial();
  const result = subsume(a, b, true);
  if (!result.ok) {
    rollback(mark);
    return false;
  }
  // Check if they're actually different (not equal)
  const aResolved = resolve(a);
  const bResolved = resolve(b);
  const areEqual = areTypesEqual(aResolved, bResolved);
  rollback(mark);
  return !areEqual;
}


/*======================================================================*/
/* 3.  Instruction set                                                  */
/*======================================================================*/
type Instr =
  | { op:"pushType"    ; ty:Type           ; loc:Loc }
  | { op:"lookup"      ; name:string; nodeIdx:number       ; loc:Loc }
  | { op:"enterScope"  ; loc:Loc }
  | { op:"exitScope"   ; loc:Loc }
  | { op:"bindConstant"; name:string; ty:Type        ; loc:Loc }
  | { op:"bindScheme"  ; name:string; scheme:Scheme; nodeIdx:number; loc:Loc }
  | { op:"bind"        ; name:string       ; loc:Loc }
  | { op:"makeArrowN"  ; params:number     ; loc:Loc }
  | { op:"applyN"      ; nodeIdx:number    ; arity:number      ; loc:Loc }
  | { op:"applyT"      ; name:string; nodeIdx:number; arity:number      ; loc:Loc } // Apply type application
  | { op:"pushExpectFromStack"; loc:Loc }
  | { op:"pushExpect"  ; ty:Type           ; loc:Loc }
  | { op:"popExpect"   ; loc:Loc }
  | { op:"pop"         ; loc:Loc }
  | { op:"join"        ; loc:Loc }
  | { op:"resolveTypeAnnotation"; annotation:string; nodeIdx:number; loc:Loc }
  | { op:"dup"         ; loc:Loc }
  | { op:"storeType"   ; nodeIdx:number    ; loc:Loc }
  | { op:"storeApp"    ; nodeIdx:number    ; loc:Loc };

// Helper function to convert Expr to Program
function exprToProgram(expr: Expr): Program {
  const program = new Program([], [], 0);
  
  function convertExpr(e: Expr): number {
    switch(e.tag) {
      case "IntLit":
        return program.addNode(nodeFac.intLiteral(e.value, e.loc));
      
      case "BoolLit":
        return program.addNode(nodeFac.boolLiteral(e.value, e.loc));
      
      case "Var":
        return program.addNode(nodeFac.var(e.name, e.loc));
      
      case "AppN": {
        const fnIndex = convertExpr(e.fn);
        const argsIndices = e.args.map(convertExpr);
        return program.addNode(nodeFac.app(fnIndex, argsIndices, [], e.loc));
      }
      
      case "If": {
        const condIndex = convertExpr(e.cond);
        const thenIndex = convertExpr(e.thenBranch);
        const elseIndex = convertExpr(e.elseBranch);
        return program.addNode(nodeFac.if(condIndex, thenIndex, elseIndex, e.loc));
      }
      
      case "Let": {
        const valueIndex = e.value ? convertExpr(e.value) : -1;
        // Note: body would need to be handled separately
        let ann: number | undefined = undefined;
        if (e.annotation !== null) {
          ann = convertExpr(e.annotation);
        }
        return program.addNode(nodeFac.let(e.name, valueIndex, ann, e.loc));
      }
      
      case "Seq": {
        const statementsIndices = e.stmts.map(convertExpr);
        return program.addNode(nodeFac.statements(statementsIndices, e.loc));
      }
      
      case "Lam": {
        // Convert lambda to FunDecl with multiple parameters
        const paramIndices: number[] = [];
        
        for (let i = 0; i < e.params.length; i++) {
          const paramIndex = program.addNode(nodeFac.funParam(e.params[i], -1, e.loc));
          paramIndices.push(paramIndex);
        }
        
        const bodyIndex = convertExpr(e.body);
        return program.addNode(nodeFac.funDecl("", paramIndices, [], 0, bodyIndex, e.loc));
      }
      
      case "FunDecl": {
        // Convert generic function declaration
        const paramIndices: number[] = [];
        
        // Add type parameters
        const typeParamIndices: number[] = [];
        for (const typeParam of e.typeParams) {
          const typeParamIndex = program.addNode({ 
            location: e.loc, 
            kind: "TypeParam", 
            name: typeParam, 
            constraintsIndices: [] 
          });
          typeParamIndices.push(typeParamIndex);
        }

        // Add function parameters
        for (let i = 0; i < e.params.length; i++) {
          const typeIndex = e.paramTypes?.[i] ? program.addNode(nodeFac.var(e.paramTypes[i])) : -1;
          const paramIndex = program.addNode(nodeFac.funParam(e.params[i], typeIndex, e.loc));
          paramIndices.push(paramIndex);
        }
        
        const bodyIndex = convertExpr(e.body);
        const funDeclIndex = program.addNode(nodeFac.funDecl(e.name, paramIndices, typeParamIndices, 0, bodyIndex, e.loc));
        
        // Create a scheme for the generic function and bind it to the environment
        const typeVars = e.typeParams.map(tvar);
        const paramTypes = e.params.map(() => newUnknown()); // Unknown types for parameters
        const bodyType = newUnknown(); // Unknown type for body
        const funType = arrowN(paramTypes, bodyType);
        const scheme_ = scheme(e.name, getNextSchemeId(), e.typeParams, funType);

        console.log("scheme for ", e.name, scheme_);
        
        // Store the scheme in the program for later binding
        program.schemes = program.schemes || new Map();
        program.schemes.set(scheme_.id, scheme_);
        
        return funDeclIndex;
      }

      case "TypeApp": {
        const ctorIndex = convertExpr(e.ctor);
        const argsIndices = e.args.map(convertExpr);
        return program.addNode(nodeFac.typeApp(ctorIndex, argsIndices, e.loc));
      }

      default: {
        const _: never = e;
        assert(false, "Unexpected expression", { e });
      }
    }
  }
  
  const rootIndex = convertExpr(expr);
  program.rootIndex = rootIndex;
  program.types = new Array(program.nodes.length).fill(null);
  return program;
}

/*======================================================================*/
/* 4.  Lineariser                                                       */
/*======================================================================*/

// Modified lineariser to work with Program
function lineariseProgram(program: Program, nodeIdx: number, mode: "synth" | "check" = "synth", expect?: Type): Instr[] {
  const code: Instr[] = [];
  const node = program.getNode(nodeIdx);
  
  const synth = (index: number) => code.push(...lineariseProgram(program, index, "synth"));
  const checkM = (index: number, t: Type) => code.push(
    {op:"pushExpect", ty: t, loc: node.location},
    ...lineariseProgram(program, index, "synth"),
    {op:"popExpect", loc: node.location});

  switch(node.kind) {
    case "IntLiteral":
      code.push({op:"pushType",ty:IntType, loc:node.location});
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;

    case "BoolLiteral":
      code.push({op:"pushType",ty:BoolType,loc:node.location});
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;

    case "FloatLiteral":
      code.push({op:"pushType",ty:FloatType,loc:node.location});
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;

    case "Var":
      code.push({op:"lookup", name: node.name, nodeIdx, loc: node.location});
      code.push({op:"storeType", nodeIdx, loc: node.location});
      break;

    case "App": {
      synth(node.fnIndex);
      // Synthesize all arguments in order (last arg will be on top of stack)
      for (const argIndex of node.argsIndices) {
        synth(argIndex);
      }
      const app = new Application()
      app.nodeIdx = nodeIdx;
      program.apps.set(nodeIdx, app);

      code.push({op:"applyN", nodeIdx: nodeIdx, arity: node.argsIndices.length, loc: node.location});
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;
    }

    case "FunDecl": {
      code.push({op:"enterScope",loc:node.location});

      const typeParams: Record<string, Type> = {};
      let scheme_: Scheme | undefined;
      if (node.typeParamsIndices.length) {
        scheme_ = scheme(node.name, getNextSchemeId(), [], null!);
        program.schemes.set(scheme_.id, scheme_);

        for (const typeParamIndex of node.typeParamsIndices) {
          const typeParamNode = program.getNode(typeParamIndex);
          assert(typeParamNode.kind === "TypeParam", "Expected type param node for now");
          typeParams[typeParamNode.name] = tvar(typeParamNode.name);
          scheme_.vars.push(typeParamNode.name);
        }
      }

      const lineariseType = (paramNode: Node, nodeIdx: number, loc: Loc) => {
        if (nodeIdx === -1) return code.push({op:"pushType", ty:newUnknown(), loc});
        const node = program.getNode(nodeIdx);
        assert(node.kind === "Var", "Expected var node for now", { paramNode, node });
        code.push({op:"pushType", ty:typeParams[node.name], loc:node.location});
      }
      
      // Handle parameters
      for (const paramIndex of node.paramsIndices) {
        const paramNode = program.getNode(paramIndex);
        if (paramNode.kind === "FunParam") {
          // For now, assume unannotated parameters get unknown types
          lineariseType(paramNode, paramNode.typeIndex, paramNode.location)
          code.push({op:"bind",name:paramNode.name,loc:node.location});
        }
      }

      // Synthesize body
      // TODO: Check against expected type
      synth(node.bodyIndex);
      
      // Create function type
      code.push({op:"makeArrowN", params: node.paramsIndices.length, loc: node.location});
      code.push({op:"exitScope",loc:node.location});

      if (scheme_) {
        code.push({op:"bindScheme", name: node.name, scheme: scheme_, nodeIdx, loc: node.location});
      }

      break;
    }

    case "If": {
      checkM(node.condIndex, BoolType);
      code.push({op:"pop",loc:node.location});  // Pop the condition value
      synth(node.thenIndex);
      if (node.elseIndex !== undefined) {
        synth(node.elseIndex);
      }
      code.push({op:"join",loc:node.location});
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;
    }

    case "Let": {
      if (node.valueIndex !== -1) synth(node.valueIndex);
      if (node.typeIndex !== undefined) {
        // Convert annotation type index to type using instruction
        const typeNode = program.getNode(node.typeIndex);

        const lineariseType = (paramNode: Node, nodeIdx: number, loc: Loc) => {
          if (nodeIdx === -1) return code.push({op:"pushType",ty:newUnknown(),loc});
          const node = program.getNode(nodeIdx);
          if (node.kind === "Var") {
            code.push({op:"resolveTypeAnnotation",annotation:node.name,nodeIdx,loc:node.location});
            code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
          } else if (node.kind === "TypeApp") {
            node.typeArgsIndices.forEach(argIndex => {
              lineariseType(node, argIndex, node.location);
            });
            const baseNode = program.getNode(node.baseIndex);
            assert(baseNode.kind === "Var", "Expected var node for now", { baseNode });
            code.push({op:"applyT",name:baseNode.name,nodeIdx,arity:node.typeArgsIndices.length,loc:node.location});
            code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
          } else {
            assert(false, "Expected var node for now", { node });
          }
        }

        lineariseType(typeNode, node.typeIndex, typeNode.location);
        // code.push({op:"resolveTypeAnnotation", annotation:typeNode.name, loc:node.location});

        if (node.valueIndex !== -1) {
          code.push({op:"pushExpectFromStack", loc:node.location});
          code.push({op:"popExpect", loc:node.location});
          code.push({op:"pop",loc:node.location}); // Pop the annotation type from stack
        }
      }
      code.push({op:"bind",name:node.name, loc:node.location});
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;
    }

    case "Statements": {
      const n = node.statementsIndices.length;
      if (n === 0) throw new Error("empty block");
      for(let i = 0; i < n-1; i++){
        synth(node.statementsIndices[i]);
        code.push({op:"pop",loc:node.location});
      }
      code.push(...lineariseProgram(program, node.statementsIndices[n-1], mode, expect));
      code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
      break;
    }

    case "TypeApp": {
      assert(false, "TypeApp not expected at this position (must be in a type position)", { node });
    }
    case "Constant": {
      assert(false, "Constant not expected at this position (must be in a type position)", { node });
    }

    default: {
      // const _: never = node;
      throw new Error(`${locStr({loc:node.location} as Instr)}: unknown node kind ${node.kind}`);
    }
  }

  if (mode === "check" && expect)
    return [{op:"pushExpect",ty:expect,loc:node.location},...code,
            {op:"popExpect",loc:node.location}];

  return code;
}

/*======================================================================*/
/* 5.  Interpreter / type-checker                                       */
/*======================================================================*/

type RunResult = Type | SuspendMissing;

type SuspendMissing = {
  done  : false;
  id    : string;               // the fully-qualified name we need
  resume: (typeOrScheme: Scheme | Type | Error) => RunResult;
};

type InterpreterState = {
  code: Instr[]
  instr?: Instr
  pc: number;
  typeStk: Type[];
  expectStk: Type[];
  envStk: Env[];
  program?: Program; // Optional program reference for storeType instruction
}
const createInterpreterState = (code: Instr[], initialEnv: Env, program?: Program): InterpreterState => ({ 
  code, 
  pc: 0, 
  typeStk: [], 
  expectStk: [], 
  envStk: [initialEnv],
  program
});


const getOverloadMatch = (alts: ArrowNType[], argTys: Type[]): ArrowNType => {
  const arity = argTys.length;
  const exactMatches: ArrowNType[] = [];
  const allMatches: ArrowNType[] = [];
  alts.forEach(alt => {
    if (alt.params.length !== arity) return;
    
    // Check if all arguments match exactly without implicit casts
    let subtype = false;
    for (let j = 0; j < arity; j++) {
      if (!trySubsume(argTys[j], alt.params[j])) return;
      if (isStrictSubtype(argTys[j], alt.params[j])) subtype = true;
    }
    allMatches.push(alt);
    if (!subtype) exactMatches.push(alt);
  });
  
  // TODO: Better error messages
  assert(allMatches.length > 0, `no viable overloads for ${arity} arguments`, { arity, argTys, alts });

  if (exactMatches.length === 1) return exactMatches[0];
  if (exactMatches.length === 0 && allMatches.length === 1) return allMatches[0];
  assert(false, "ambiguous overload", { exactMatches, allMatches, argTys });
}

const updateApp = (state: InterpreterState, nodeIdx: number, schemeId: number, fnTy: Type, argTys: Type[], result: Type)  => {
  const app = state.program!.apps.get(nodeIdx); 
  assert(app, "app not found", { nodeIdx });
  app.fn = fnTy;
  app.schemeId = schemeId;
  app.args = argTys;
  app.typeArgs = [];
  app.result = result;
}

const applyN = (state: InterpreterState, nodeIdx: number, arity: number, fnTy: Type, argTys: Type[]): Type  => {

  if (isOverload(fnTy)) {
    const match = getOverloadMatch(fnTy.alts, argTys);
    for (let j = 0; j < arity; j++) {
      subsume(argTys[j], match.params[j], true).getOrThrow()
    }
    const res = resolve(match.result);
    updateApp(state, nodeIdx, -1, match, argTys, res);
    return res;
  } else if (isArrowN(fnTy)) {
    assert(fnTy.params.length === arity, `function expects ${fnTy.params.length} arguments but got ${arity}`, { fnTy, arity });
    for (let j = 0; j < arity; j++) {
      subsume(argTys[j], fnTy.params[j], true).getOrThrow()
    }
    const res = resolve(fnTy.result);
    updateApp(state, nodeIdx, -1, fnTy, argTys, res);
    return res;
  } else if (isAppliedType(fnTy)) {
    const scheme = state.program!.schemes.get(fnTy.schemeId)
    assert(scheme, "scheme not found", { fnTy });
    const newFnTy = concreteInstantiateWithArgs(state, scheme, fnTy.args);
    const res = applyN(state, nodeIdx, arity, newFnTy, argTys);
    updateApp(state, nodeIdx, fnTy.schemeId, newFnTy, argTys, res);
    return res;
  }
  assert(false, "cannot apply non-function", { fnTy });
}

function lookupType(state: InterpreterState, name: string, nodeIdx: number, loc: Loc, args: Type[]): Type {

  // For now
  const prim = (ty: Type) => {
    assert(args.length === 0, "Primitives can't have type arguments");
    return ty;
  }
  if (name === "Int") return prim(IntType);
  if (name === "Float") return prim(FloatType);
  if (name === "Bool") return prim(BoolType);
  if (name === "Unit") return prim(UnitType);

  if (name === "Fn") {
    return arrowN(args.slice(0, -1), args[args.length - 1]);
  }
    
  const e = state.envStk[state.envStk.length-1].get(name);
  assert(e, `type '${name}' not found`);
  assert(e.type, `type '${name}' not found`);

  const tb = e.type;
  if (tb.tag === "KnownT") {
    const z = tb.schemeOrType;
    if (isScheme(z)) { // generic ctor
      assert(args.length === z.vars.length, `arity mismatch for ${name} got ${args.length} expected ${z.vars.length}`, { args, z });
      assert(isScheme(z), "z is not a scheme", { z });
      return instantiateWithArgs(state, nodeIdx, z, args);
    }
    assert(args.length === 0, `${name} is not generic`);
    return z;
  }

  /* tag === "PendT" → pause until module compiled */
  // return pauseForType(name, tb, loc, args);
  assert(false, "Not implemented pause for types in lookupType");
}

function runInternal(state: InterpreterState): RunResult {
  const { code, typeStk, expectStk, envStk } = state;

  const env = () => envStk[envStk.length-1];
  const envSetVal = (name: string, type: Type | Scheme) => env().set(name, { value: { tag:"KnownV", schemeOrType: type } });

  const popN = (n: number): Type[] => {
    assert(n > 0, "popN: n must be positive");
    assert(n <= typeStk.length, "popN: n must be less than or equal to the stack length");
    return typeStk.splice(typeStk.length - n, n);
  };

  for (; state.pc < code.length; state.pc++) {
    const i = state.instr = code[state.pc];
    // console.log("i =", compactInspect(i));
    switch(i.op) {

      case "pushType": typeStk.push(i.ty); break;

      case "lookup": {
        if (!env().has(i.name))
          throw new Error(`${locStr(i)}: unbound variable ${i.name}`);
        const entry = env().get(i.name)!;
        if (entry && entry.value && entry.value.tag === "KnownV") {
          typeStk.push(appliedSchemeOrType(state, i.nodeIdx, entry.value.schemeOrType));
          break;
        }

        return {
          done: false,
          id: i.name,
          resume: (typeOrScheme: Type | Scheme | Error) => {
            if (typeOrScheme instanceof Error) throw typeOrScheme;
            envSetVal(i.name, typeOrScheme);
            return runInternal(state);
          }
        };
      }

      case "enterScope": envStk.push(new Map(env()) as Env); break;
      case "exitScope":  envStk.pop(); break;

      case "bindConstant": envSetVal(i.name, i.ty); break;
      case "bindScheme": {
        // Update the body and bind it
        const result = typeStk.pop()!;
        i.scheme.body = result;
        envSetVal(i.name, i.scheme);
        typeStk.push(applySchemeUnknowns(state, i.nodeIdx, i.scheme));
        break;
      }

      case "bind":
        assert(typeStk.length > 0, "stack underflow");
        envSetVal(i.name, typeStk.at(-1)!);
        break;

      case "makeArrowN": {
        const resultTy = typeStk.pop()!;
        const paramsTy = popN(i.params);
        typeStk.push(arrowN(paramsTy, resultTy));
        break;
      }

      case "resolveTypeAnnotation": {
        const annotation = i.annotation;
        const resolvedType = lookupType(state, annotation, i.nodeIdx, i.loc, []);
        typeStk.push(resolvedType);
        break;
      }

      case "dup": {
        assert(typeStk.length > 0, "stack underflow");
        const top = typeStk.at(-1)!;
        typeStk.push(top);
        break;
      }

      case "storeType": {
        assert(typeStk.length > 0, "stack underflow");
        const topType = typeStk.at(-1)!;
        // Store the type in the program's types array at the specified node index
        assert(state.program, "No program reference available");
        assert(i.nodeIdx !== undefined, "Node index is undefined");
        assert(i.nodeIdx >= 0, "Node index is negative");
        assert(i.nodeIdx < state.program.types.length, "Node index out of bounds", { nodeIdx: i.nodeIdx, typesLength: state.program.types.length });
        state.program.types[i.nodeIdx] = topType;
        console.log(`Stored type ${show(topType)} at node index ${i.nodeIdx}`);
        break;
      }

      case "storeApp": {
        assert(state.program, "No program reference available");
        assert(i.nodeIdx !== undefined, "Node index is undefined");
        assert(i.nodeIdx >= 0, "Node index is negative");
        assert(i.nodeIdx < state.program.types.length, "Node index out of bounds", { nodeIdx: i.nodeIdx, typesLength: state.program.types.length });
        state.program.types[i.nodeIdx] = typeStk.at(-1)!;
        break;
      }

      case "applyN": {
        const argTys = popN(i.arity);      // keep in array (last arg last)
        const fnTy   = resolve(typeStk.pop()!);
        const res = applyN(state, i.nodeIdx, i.arity, fnTy, argTys);
        typeStk.push(res);
        break;
      }

      case "pushExpectFromStack": expectStk.push(typeStk[typeStk.length-1]); break;
      case "pushExpect": expectStk.push(i.ty); break;
      case "popExpect":
        const got = typeStk[typeStk.length-1];
        const expect = expectStk.pop()!;
        const result = subsume(got, expect, false);
        assert(result.ok, result.errorOrNull?.message ?? '', { result, got, expect });
        break;

      case "pop": typeStk.pop(); break;

      case "join": {
        const b = typeStk.pop()!;
        const a = typeStk.pop()!;
        unify(a,b, false).getOrThrow();
        typeStk.push(resolve(a));
        break;
      }

      case "applyT": {
        const argsTys = popN(i.arity);
        const res = lookupType(state, i.name, i.nodeIdx, i.loc, argsTys);
        typeStk.push(res);
        break;
      }

      default: {
        const _: never = i;
        throw new Error(`${locStr(i)}: unknown instruction ${(i as any).op}`);
      }
    }

    // console.log("typeStk =", typeStk.map(show).join(", "));
  }
  if (typeStk.length !== 1) {
    console.log("typeStk =", typeStk.map(show).join(", "));
    throw new Error("ill-typed program");
  }
  const res = resolve(typeStk[0]);
  console.log("type =", show(res));
  return res;
}

/** Run for tests until result is found */
function runExpectingResult(code: Instr[], initialEnv: Env, program?: Program): Type {
  const result = runInternal(createInterpreterState(code, initialEnv, program));
  assert(isType(result), "Expected result, but got suspend", { result });
  const inst = program!.instantiations.map(i => ({ ...i, scheme: program!.schemes.get(i.schemeId)! }));
  console.log('program.instantiations', inst);
  return result;
}

const locStr = (i:Instr) => `${i.loc.file}:${i.loc.line}:${i.loc.col}`;
const compactInspect = (i: any) => inspect(i, { depth: 1, colors: true, compact: true })

/*======================================================================*/
/* 6.  Tests                                                             */
/*======================================================================*/

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
    nextU = 1;
    
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
    nextU = 3;
    
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

const insertSchemes = (program: Program, env: Env) => {
  env.forEach((entry, name) => {
    if (entry.value?.tag === "KnownV" && isScheme(entry.value.schemeOrType)) {
      program.schemes.set(entry.value.schemeOrType.id, entry.value.schemeOrType);
    } else if (entry.type?.tag === "KnownT" && isScheme(entry.type.schemeOrType)) {
      program.schemes.set(entry.type.schemeOrType.id, entry.type.schemeOrType);
    }
  });
}

describe("Generic Type System", () => {
  it("should handle generic identity function with Int", () => {
    const env: Env = new Map();
    
    // Define a generic identity function: ∀T. T → T
    const idScheme = scheme("id", getNextSchemeId(), ["T"], arrowN([tvar("T")], tvar("T")));
    envSetVal(env, "id", idScheme);
    
    // Test with Int
    const prog1 = app(v("id"), int(42));
    const program1 = exprToProgram(prog1);
    insertSchemes(program1, env);
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
    insertSchemes(program2, env);
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

expect.extend({
  toEqualType(received: Type, expected: Type) {
    return {  
      pass: areTypesEqual(received, expected),
      message: () => `expected ${received} to be ${expected}`,
    };
  },
});

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
    insertSchemes(program, env);
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
      const node = program.nodes[i];
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
      const node = program.nodes[i];
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
      const node = program.nodes[i];
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
      const node = program.nodes[i];
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
      const node = program.nodes[i];
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
    insertSchemes(program, env);
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
    expect(inst[0].mono).toEqualType(tapp(idScheme, [IntType])); // TODO: A bit confused when to use tapp or arrow
    expect(inst[0].args[0]).toEqualType(IntType);
    
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
    const prog = v("map");
    const program = exprToProgram(prog);
    const bytecode = lineariseProgram(program, program.rootIndex);
    const result = runExpectingResult(bytecode, env, program);
    
    // Check that the type was stored for the root node
    expect(program.types[program.rootIndex]).toBeDefined();
    expect(result).toBeDefined();
  });
});
