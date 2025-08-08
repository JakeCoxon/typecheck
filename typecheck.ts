import { inspect } from "bun";

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
  [inspect.custom as any]: (d: any, o: any, i: any) => o.stylize(`<loc>`, 'special') };   // demo helper

/*======================================================================*/
/* 1.  Types, unknowns, occurs-check unification                        */
/*======================================================================*/

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
  toString() { return `?${this.id}` }
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
  toString() { return show(this, null) }
}

// Overload type (from bidi)
export class OverloadType extends TypeRoot {
  constructor(public alts: ArrowNType[]) { super() }
  toString() { return show(this, null) }
}

// Struct type (aligning with defs.ts)
export class StructType extends TypeRoot {
  constructor(public name: string, public fields: { name: string; type: Type }[]) { super() }
  toString() { return show(this, null) }
}

// Type application (aligning with defs.ts)
export class AppliedType extends TypeRoot {
  constructor(public ctor: string, public schemeId: number, public args: Type[]) { super() }
  toString() { return show(this, null) }
}

// Type parameter declaration (aligning with defs.ts)
export class TypeParameterDecl extends TypeRoot {
  constructor(public name: string, public constraints: Type[], public scopeId: string) { super() }
  toString() { return show(this, null) }
}

// Type constraints system
export type Bound =
  | { kind: "Trait"; tvar: string; traitId: number }
  | { kind: "Subtype"; tvar: string; upper: Type };

// Scheme for polymorphic types (extended with bounds)
export interface Scheme { 
  name: string; 
  id: number; 
  vars: string[]; 
  body: Type;
  bounds?: Bound[];
}

// Trait catalogue & impl DB
export interface Trait { id: number; name: string }

// Helper function to generate a unique key for a type
function typeKey(t: Type, builder: ProgramBuilder): string {
  t = resolve(t, builder);
  if (isUnknown(t)) return `?${t.id}`;
  if (isTVar(t)) return t.name;
  if (isPrimitive(t)) return t.name;
  if (isTApp(t)) return `${t.ctor}<${t.args.map(arg => typeKey(arg, builder)).join(",")}>`;
  if (isArrowN(t)) return `(${t.params.map(arg => typeKey(arg, builder)).join(",")}→${typeKey(t.result, builder)})`;
  if (isStructType(t)) return `${t.name}{${t.fields.map(f => `${f.name}:${typeKey(f.type, builder)}`).join(",")}}`;
  if (isOverload(t)) return `{${t.alts.map(alt => typeKey(alt, builder)).join("|")}}`;
  return "unknown";
}

export const hasTrait = (ty: Type, traitId: number, builder: ProgramBuilder): boolean =>
  builder.traitImpls.has(`${traitId}|${typeKey(ty, builder)}`);

// Helper function to check if a type contains unknowns
function containsUnknown(t: Type, builder: ProgramBuilder): boolean {
  t = resolve(t, builder);
  if (isUnknown(t)) return true;
  if (isArrowN(t)) return t.params.some(p => containsUnknown(p, builder)) || containsUnknown(t.result, builder);
  if (isOverload(t)) return t.alts.some(alt => {
    if (isArrowN(alt)) return alt.params.some(p => containsUnknown(p, builder)) || containsUnknown(alt.result, builder);
    return false;
  });
  if (isTApp(t)) return t.args.some(arg => containsUnknown(arg, builder));
  if (isStructType(t)) return t.fields.some(f => containsUnknown(f.type, builder));
  return false;
}

// Helper function to generate canonical key for instantiation
function canonicalKey(schemeId: number, args: Type[], builder: ProgramBuilder): string {
  return JSON.stringify({ schemeId, args: args.map(arg => typeKey(arg, builder)) });
}

// Obligations: create now, check now or later
export type Obligation =
  | { kind: "Trait"; traitId: number; ty: Type; loc: Loc; instKey: string }
  | { kind: "Subtype"; left: Type; right: Type; loc: Loc; instKey: string };


// Helper function to fail with a location-aware error
function fail(loc: Loc, message: string): never {
  throw new Error(`${loc.file}:${loc.line}:${loc.col}: ${message}`);
}

// Convert bounds(TVar) → obligations(TypeArg) and either check or defer
function emitObligationsForInstantiation(s: Scheme, args: Type[], loc: Loc, instKey: string, b: ProgramBuilder) {
  if (!s.bounds) return;
  
  const sub = new Map<string, Type>();
  s.vars.forEach((v, i) => sub.set(v, args[i]!));

  for (const bound of s.bounds) {
    switch (bound.kind) {
      case "Trait": {
        const ty = substWalk(tvar(bound.tvar), sub);
        const ob: Obligation = { kind: "Trait", traitId: bound.traitId, ty, loc, instKey };
        tryCheckOrDefer(ob, b);
        break;
      }
      case "Subtype": {
        const left = substWalk(tvar(bound.tvar), sub);
        const right = substWalk(bound.upper, sub);
        const ob: Obligation = { kind: "Subtype", left, right, loc, instKey };
        tryCheckOrDefer(ob, b);
        break;
      }
    }
  }
}

function tryCheckOrDefer(ob: Obligation, b: ProgramBuilder) {
  // If any side still has Unknowns, we can't decide now → defer.
  if (ob.kind === "Trait") {
    if (containsUnknown(ob.ty, b)) { 
      b.pendingObligations.push(ob); 
      return; 
    }
    if (!hasTrait(ob.ty, ob.traitId, b)) {
      const traitName = b.traitTable.get(ob.traitId)?.name || `trait_${ob.traitId}`;
      fail(ob.loc, `type ${show(ob.ty, b)} does not implement ${traitName}`);
    }
  } else {
    if (containsUnknown(ob.left, b) || containsUnknown(ob.right, b)) { 
      b.pendingObligations.push(ob); 
      return; 
    }
    // Use your ≤ checker (subsume) *speculatively* with rollback to avoid side-effects
    const mark = startTrial(b);
    try { 
      subsume(ob.left, ob.right, true, b).getOrThrow(); 
      rollback(mark, b); 
    } catch { 
      rollback(mark, b); 
      fail(ob.loc, `constraint not satisfied: ${show(ob.left, b)} ≤ ${show(ob.right, b)}`); 
    }
  }
}

// Substitution function for type variables (used in emitObligationsForInstantiation)
function substWalk(t: Type, subst: Map<string, Type>): Type {
  if (isTVar(t)) {
    const replacement = subst.get(t.name);
    return replacement ? replacement : t;
  }
  if (isUnknown(t)) {
    return t; // Unknown types are not substituted
  }
  if (isArrowN(t)) {
    return arrowN(t.params.map(p => substWalk(p, subst)), substWalk(t.result, subst));
  }
  if (isOverload(t)) {
    return overload(t.alts.map(alt => {
      return arrowN(alt.params.map(p => substWalk(p, subst)), substWalk(alt.result, subst));
    }));
  }
  if (isTApp(t)) {
    // For AppliedType, just substitute the args
    return new AppliedType(t.ctor, t.schemeId, t.args.map(arg => substWalk(arg, subst)));
  }
  if (isStructType(t)) {
    const struct = t as StructType;
    return tstruct(struct.name, struct.fields.map(f => ({ name: f.name, type: substWalk(f.type, subst) })));
  }
  if (isPrimitive(t)) {
    return t; // Primitive types are not substituted
  }
  // For any other type, return as-is
  return t;
}

// Function to require trait now (for checking inside generic bodies)
function requireTraitNow(ty: Type, traitId: number, loc: Loc, builder: ProgramBuilder) {
  ty = resolve(ty, builder);

  if (isTVar(ty)) {
    if (!builder.activeTraitBounds.get(ty.name)?.has(traitId)) {
      const traitName = builder.traitTable.get(traitId)?.name || `trait_${traitId}`;
      fail(loc, `Using a value of type ${ty.name} requires ${traitName}; add it to the function's bounds`);
    }
    return;
  }
  // concrete types can be checked immediately
  if (!hasTrait(ty, traitId, builder)) {
    const traitName = builder.traitTable.get(traitId)?.name || `trait_${traitId}`;
    fail(loc, `type ${show(ty, builder)} does not implement ${traitName}`);
  }
}

// Function to discharge deferred obligations (call after type solving)
function dischargeDeferredObligations(state: InterpreterState) {
  const b = state.builder;
  for (const ob of b.pendingObligations) {
    if (ob.kind === "Trait") {
      const t = resolve(ob.ty, b);
      if (!hasTrait(t, ob.traitId, b)) {
        const traitName = b.traitTable.get(ob.traitId)?.name || `trait_${ob.traitId}`;
        fail(ob.loc, `type ${show(t, b)} does not implement ${traitName}`);
      }
    } else {
      const L = resolve(ob.left, b), R = resolve(ob.right, b);
      const mark = startTrial(b);
      try { 
        subsume(L, R, true, b).getOrThrow(); 
        rollback(mark, b); 
      } catch { 
        rollback(mark, b); 
        fail(ob.loc, `constraint not satisfied: ${show(L, b)} ≤ ${show(R, b)}`); 
      }
    }
    // (optional) attach the (traitId,type) to the specialisation entry keyed by ob.instKey
    // attachRequiredImpl(ob.instKey, ob);
  }
  b.pendingObligations.length = 0;
}

// Helper functions to register traits and implementations
function registerTrait(builder: ProgramBuilder, id: number, name: string): void {
  builder.traitTable.set(id, { id, name });
}

function registerTraitImpl(builder: ProgramBuilder, traitId: number, type: Type): void {
  builder.traitImpls.set(`${traitId}|${typeKey(type, builder)}`, true);
}

// Helper function to create bounds for a scheme
function createBounds(traitBounds: Array<{ tvar: string; traitId: number }>, subtypeBounds: Array<{ tvar: string; upper: Type }> = []): Bound[] {
  const bounds: Bound[] = [];
  
  for (const { tvar, traitId } of traitBounds) {
    bounds.push({ kind: "Trait", tvar, traitId });
  }
  
  for (const { tvar, upper } of subtypeBounds) {
    bounds.push({ kind: "Subtype", tvar, upper });
  }
  
  return bounds;
}

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

const areTypesEqual = (t1: Type, t2: Type, builder: ProgramBuilder): boolean => {
  t1 = resolve(t1, builder);
  t2 = resolve(t2, builder);
  const areTypeListsEqual = (l1: Type[], l2: Type[]): boolean => l1.length === l2.length && l1.every((t, i) => areTypesEqual(t, l2[i]!, builder));
  if (t1 === t2) return true;
  if (t1 instanceof UnknownType && t2 instanceof UnknownType) return t1.id === t2.id;
  if (t1 instanceof TypeVariable && t2 instanceof TypeVariable) return t1.name === t2.name;
  if (t1 instanceof PrimitiveType && t2 instanceof PrimitiveType) return t1.name === t2.name;
  if (t1 instanceof ArrowNType && t2 instanceof ArrowNType) return areTypeListsEqual(t1.params, t2.params) && areTypesEqual(t1.result, t2.result, builder);
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
const newUnknown = (b: ProgramBuilder): UnknownType => new UnknownType(b.nextU++);
const tvar = (name: string): TypeVariable => new TypeVariable(name);
const tapp = (scheme: Scheme, args: Type[]): AppliedType => new AppliedType(scheme.name, scheme.id, args);
const tstruct = (name: string, fields: { name: string; type: Type }[]): StructType => new StructType(name, fields);
const arrow = (param: Type, result: Type): ArrowNType => new ArrowNType([param], result);
const arrowN = (params: Type[], result: Type): ArrowNType => new ArrowNType(params, result);
const overload = (alts: ArrowNType[]): OverloadType => new OverloadType(alts);
const scheme = (name: string, id: number, vars: string[], body: Type, bounds?: Bound[]): Scheme => ({ name, id, vars, body, bounds });

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


class Application {
  schemeId!: number
  nodeIdx!: number
  fn!: Type
  args!: Type[]
  typeArgs!: Type[]
  result!: Type
}

class Instantiation {
  schemeId!: number
  args!: Type[]
  mono!: Type
  nodeIdx!: number
}



export class ProgramBuilder {
  // Building-time state
  public nodes: Node[] = [];
  public types: Type[] = [];
  public schemes: Map<number, Scheme> = new Map();
  public apps: Map<number, Application> = new Map();
  public instantiations: Instantiation[] = [];
  public program?: Program;

  // Type inference state (needed during building)
  public solved: Map<number, Type> = new Map();
  public trail: Array<{u: UnknownType; prev: Type | undefined}> = [];
  public nextU: number = 0;
  public nextSchemeId: number = 0;
  
  // Constraint system state (needed during building)
  public traitTable: Map<number, Trait> = new Map();
  public traitImpls: Map<string, true> = new Map();
  public pendingObligations: Obligation[] = [];
  public activeTraitBounds: Map<string, Set<number>> = new Map();
  
  // Primitive subtyping (needed during building)
  public primLe: Record<string, string[]> = {
    Int: ["Int", "Float"],
    Float: ["Float"],
    Bool: ["Bool"],
    Unit: ["Unit"],
  };

  constructor() {}

  // Simple helper method for adding nodes
  addNode(node: Node): number {
    const index = this.nodes.length;
    this.nodes.push(node);
    return index;
  }

  scheme(name: string, vars: string[], body: Type, bounds?: Bound[]): Scheme {
    const id = this.nextSchemeId++;
    return { name, id, vars, body, bounds };
  }
}

const getNextSchemeId = (b: ProgramBuilder) => b.nextSchemeId++;


// Program class to hold the indexed arrays
export class Program {
  constructor(
    public readonly nodes: Node[],
    public readonly types: Type[],
    public readonly rootIndex: number,
    public readonly schemes: Map<number, Scheme>,
    public readonly apps: Map<number, Application>,
    public readonly instantiations: Instantiation[]
  ) {}

  // Helper methods to work with the indexed structure
  getNode(index: number): Node {
    if (index < 0 || index >= this.nodes.length) {
      throw new Error(`Invalid node index: ${index}`);
    }
    const node = this.nodes[index];
    assert(node, `Node at index ${index} is undefined`);
    return node;
  }

  getType(index: number): Type {
    if (index < 0 || index >= this.types.length) {
      throw new Error(`Invalid type index: ${index}`);
    }
    const type = this.types[index];
    assert(type, `Type at index ${index} is undefined`);
    return type;
  }

  getScheme(id: number): Scheme | undefined {
    return this.schemes.get(id);
  }

  getApp(nodeIdx: number): Application | undefined {
    return this.apps.get(nodeIdx);
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


function startTrial(builder: ProgramBuilder): number {
  const trailArray = builder.trail;
  return trailArray.length;
}

function rollback(mark: number, builder: ProgramBuilder): void {
  const trailArray = builder.trail;
  const solvedMap = builder.solved;
  
  while (trailArray.length > mark) {
    const { u, prev } = trailArray.pop()!;
    if (prev === undefined) {
      solvedMap.delete(u.id);
    } else {
      solvedMap.set(u.id, prev);
    }
  }
}

function commit(mark: number, builder: ProgramBuilder): void {
  const trailArray = builder.trail;
  trailArray.length = mark;
}

const primLe: Record<string, string[]> = {
  Int  : ["Int",  "Float"],   // Int  ≤  Int   and  Int ≤ Float
  Float: ["Float"],
  Bool : ["Bool"],
  Unit : ["Unit"],
};

const primSubtype = (a: PrimitiveType, b: PrimitiveType): boolean => 
  a === b || (primLe[a.name]?.includes(b.name) ?? false);

// Simple resolve - only resolves root-level unknowns
const resolve = (t: Type, builder: ProgramBuilder): Type => {
  const solvedMap = builder.solved;
  
  if (isUnknown(t) && solvedMap.has(t.id)) {
    return resolve(solvedMap.get(t.id)!, builder);
  }
  
  return t;
};

// Deep resolve - recursively resolves unknowns within compound types
const resolveRecursive = (t: Type, builder: ProgramBuilder): Type => {
  const solvedMap = builder.solved;
  
  if (isUnknown(t) && solvedMap.has(t.id)) {
    return resolveRecursive(solvedMap.get(t.id)!, builder);
  }
  
  // Recursively resolve compound types
  if (isArrowN(t)) {
    const resolvedParams = t.params.map(p => resolveRecursive(p, builder));
    const resolvedResult = resolveRecursive(t.result, builder);
    return arrowN(resolvedParams, resolvedResult);
  }
  
  if (isOverload(t)) {
    return overload(t.alts.map(alt => resolveRecursive(alt, builder) as ArrowNType));
  }
  
  if (isTApp(t)) {
    return new AppliedType(t.ctor, t.schemeId, t.args.map(arg => resolveRecursive(arg, builder)));
  }
  
  if (isStructType(t)) {
    return tstruct(t.name, t.fields.map(f => ({ name: f.name, type: resolveRecursive(f.type, builder) })));
  }
  
  return t;
};

function occurs(u: UnknownType, t: Type, b: ProgramBuilder): boolean {
  t = resolve(t, b);
  if (t === u) return true;
  if (isArrowN(t)) return t.params.some(p => occurs(u, p, b)) || occurs(u, t.result, b);
  if (isOverload(t)) return t.alts.some(alt => {
    if (isArrowN(alt)) return alt.params.some(p => occurs(u, p, b)) || occurs(u, alt.result, b);
    return false;
  });
  if (isTApp(t)) return t.args.some(arg => occurs(u, arg, b));
  return false;
}


const unify = Result.wrap((a: Type, b: Type, record: boolean = true, builder: ProgramBuilder) => {
  a = resolve(a, builder); b = resolve(b, builder);
  if (a === b) return;

  if (isUnknown(a)) {
    if (occurs(a, b, builder)) throw new Error(`infinite type in ${show(b, builder)}`);
    bindUnknown(a, b, record, builder); return;
  }
  if (isUnknown(b)) { return unify(b, a, record, builder); }

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
      unify(a.params[i]!, b.params[i]!, record, builder).getOrThrow()
    }
    unify(a.result, b.result, record, builder).getOrThrow()
    return;
  }
  if (isOverload(a) && isOverload(b)) {
    assert(a.alts.length === b.alts.length, "cannot unify overloads with different numbers of alternatives", { a, b })
    for (let i = 0; i < a.alts.length; i++) {
      unify(a.alts[i]!, b.alts[i]!, record, builder).getOrThrow()
    }
    return;
  }
  if (isTApp(a) && isTApp(b)) {
    assert(a.ctor === b.ctor, "cannot unify type applications with different constructors", { a, b })
    assert(a.args.length === b.args.length, "cannot unify type applications with different numbers of arguments", { a, b })
    for (let i = 0; i < a.args.length; i++) {
      unify(a.args[i]!, b.args[i]!, record, builder).getOrThrow()
    }
    return;
  }
  if (isPrimitive(a) && isPrimitive(b) && a.name === b.name) return;
  assert(false, "cannot unify", { a, b })
}, handleAssertionOrThrow);

/** returns true and may bind unknowns  */
const subsume = Result.wrap((a: Type, b: Type, record: boolean = true, builder: ProgramBuilder) => {
  a = resolve(a, builder);  b = resolve(b, builder);
  if (a === b) return;

  // unknowns behave like Algorithm W instantiation / generalisation
  if (isUnknown(a)) { bindUnknown(a, b, record, builder); return; }
  if (isUnknown(b)) { bindUnknown(b, a, record, builder); return; }

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
      subsume(a.params[i]!, b.params[i]!, record, builder).getOrThrow()
    }
    subsume(a.result, b.result, record, builder).getOrThrow()
    return;
  }

  // type application: structural equality
  if (isTApp(a) && isTApp(b)) {
    assert(a.ctor === b.ctor, "cannot subsume type applications with different constructors", { a, b })
    assert(a.args.length === b.args.length, "cannot subsume type applications with different numbers of arguments", { a, b })
    for (let i = 0; i < a.args.length; i++) {
      subsume(a.args[i]!, b.args[i]!, record, builder).getOrThrow()
    }
    return;
  }

  // overload types: check if all alternatives in a are subtypes of some alternative in b
  if (isOverload(a) && isOverload(b)) {
    for (const altA of a.alts) {
      let foundMatch = false;
      for (const altB of b.alts) {
        if (subsume(altA, altB, record, builder).ok) {
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

function bindUnknown(u: UnknownType, t: Type, record: boolean = true, builder: ProgramBuilder) {
  if (occurs(u,t, builder))   // reuse the occurs-check we already had
    throw new Error(`infinite type: ${show(u, builder)} in ${show(t, builder)}`);
  
  if (record) builder.trail.push({ u, prev: builder.solved.get(u.id) });
  builder.solved.set(u.id, t);
}


function appliedSchemeOrType(state: InterpreterState, nodeIdx: number, t: Type | Scheme): Type {
  if (isScheme(t)) return applySchemeUnknowns(state, nodeIdx, t);
  return t;
}

// Instantiate a scheme with fresh unknowns
function applySchemeUnknowns(state: InterpreterState, nodeIdx: number, s: Scheme): Type {
  const actualArgs = s.vars.map(v => newUnknown(state.builder));
  const t = tapp(s, actualArgs);
  const instKey = canonicalKey(s.id, actualArgs, state.builder);
  state.builder.instantiations.push({ schemeId: s.id, args: actualArgs, mono: t, nodeIdx });
  state.builder.schemes.set(s.id, s);
  // Emit obligations (may defer)
  emitObligationsForInstantiation(s, actualArgs, dummy, instKey, state.builder);
  return t;
}

function concreteInstantiateWithArgs(state: InterpreterState, s: Scheme, args: Type[]): Type {
  assert(args.length === s.vars.length, "arity mismatch for scheme", { s, args });
  const subst = new Map<string, Type>();
  s.vars.forEach((v, i) => subst.set(v, args[i]!));
  return substWalk(s.body, subst);
}

function instantiateWithArgs(state: InterpreterState, nodeIdx: number, s: Scheme, args: Type[]): Type {
  assert(args.length === s.vars.length, "arity mismatch for scheme", { s, args });
  const t = tapp(s, args);
  const instKey = canonicalKey(s.id, args, state.builder);
  state.program?.instantiations.push({ schemeId: s.id, args, mono: t, nodeIdx });
  state.program?.schemes.set(s.id, s);
  // Emit obligations (may defer)
  emitObligationsForInstantiation(s, args, dummy, instKey, state.builder);
  return t;
}


function show(t: Type, b: ProgramBuilder | null): string {
  if (b) t = resolve(t, b);
  if (isUnknown(t))  return `?${t.id}`;
  if (isTVar(t)) return t.name;
  if (isPrimitive(t)) return t.name;
  if (isTApp(t)) return `${t.ctor}<${t.args.map(a => show(a, b)).join(", ")}>`;
  if (isArrowN(t)) return `(${t.params.map(a => show(a, b)).join(", ")} → ${show(t.result, b)})`;
  if (isStructType(t)) return `${t.name}{${t.fields.map(f => `${f.name}: ${show(f.type, b)}`).join(", ")}}`;
  if (isOverload(t)) return `{${t.alts.map(a => show(a, b)).join(" | ")}}`;
  assert(false, "unexpected type", { name: (t as any).constructor?.name });
}

/*======================================================================*/
/* Overload resolution helpers                                           */
/*======================================================================*/

// Try to subsume a with b, return true if successful, false otherwise
function trySubsume(a: Type, b: Type, builder: ProgramBuilder): boolean {
  const mark = startTrial(builder);
  const result = subsume(a, b, true, builder);
  rollback(mark, builder);
  return result.ok;
}

// Check if a is a strict subtype of b (a < b)
function isStrictSubtype(a: Type, b: Type, builder: ProgramBuilder): boolean {
  const mark = startTrial(builder);
  const result = subsume(a, b, true, builder);
  if (!result.ok) {
    rollback(mark, builder);
    return false;
  }
  // Check if they're actually different (not equal)
  const aResolved = resolve(a, builder);
  const bResolved = resolve(b, builder);
  const areEqual = areTypesEqual(aResolved, bResolved, builder);
  rollback(mark, builder);
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
  | { op:"bindType"    ; name:string; ty:Type        ; loc:Loc }
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
  | { op:"storeApp"    ; nodeIdx:number    ; loc:Loc }
  | { op:"unknown"     ; loc:Loc };

// Helper function to convert Expr to Program
function exprToProgram(expr: Expr, builder: ProgramBuilder): Program {
  function convertExpr(e: Expr): number {
    assert(builder, "builder is required");
    switch(e.tag) {
      case "IntLit":
        return builder.addNode(nodeFac.intLiteral(e.value, e.loc));
      
      case "BoolLit":
        return builder.addNode(nodeFac.boolLiteral(e.value, e.loc));
      
      case "Var":
        return builder.addNode(nodeFac.var(e.name, e.loc));
      
      case "AppN": {
        const fnIndex = convertExpr(e.fn);
        const argsIndices = e.args.map(convertExpr);
        return builder.addNode(nodeFac.app(fnIndex, argsIndices, [], e.loc));
      }
      
      case "If": {
        const condIndex = convertExpr(e.cond);
        const thenIndex = convertExpr(e.thenBranch);
        const elseIndex = convertExpr(e.elseBranch);
        return builder.addNode(nodeFac.if(condIndex, thenIndex, elseIndex, e.loc));
      }
      
      case "Let": {
        const valueIndex = e.value ? convertExpr(e.value) : -1;
        // Note: body would need to be handled separately
        let ann: number | undefined = undefined;
        if (e.annotation !== null) {
          ann = convertExpr(e.annotation);
        }
        return builder.addNode(nodeFac.let(e.name, valueIndex, ann, e.loc));
      }
      
      case "Seq": {
        const statementsIndices = e.stmts.map(convertExpr);
        return builder.addNode(nodeFac.statements(statementsIndices, e.loc));
      }
      
      case "Lam": {
        // Convert lambda to FunDecl with multiple parameters
        const paramIndices: number[] = [];
        
        for (let i = 0; i < e.params.length; i++) {
          const paramIndex = builder.addNode(nodeFac.funParam(e.params[i]!, -1, e.loc));
          paramIndices.push(paramIndex);
        }
        
        const bodyIndex = convertExpr(e.body);
        return builder.addNode(nodeFac.funDecl("", paramIndices, [], 0, bodyIndex, e.loc));
      }
      
      case "FunDecl": {
        // Convert generic function declaration
        const paramIndices: number[] = [];
        
        // Add type parameters
        const typeParamIndices: number[] = [];
        for (const typeParam of e.typeParams) {
          const typeParamIndex = builder.addNode({ 
            location: e.loc, 
            kind: "TypeParam", 
            name: typeParam, 
            constraintsIndices: [] 
          });
          typeParamIndices.push(typeParamIndex);
        }

        // Add function parameters
        for (let i = 0; i < e.params.length; i++) {
          const typeIndex = e.paramTypes?.[i] ? builder.addNode(nodeFac.var(e.paramTypes[i]!)) : -1;
          const paramIndex = builder.addNode(nodeFac.funParam(e.params[i]!, typeIndex, e.loc));
          paramIndices.push(paramIndex);
        }
        
        const bodyIndex = convertExpr(e.body);
        const funDeclIndex = builder.addNode(nodeFac.funDecl(e.name, paramIndices, typeParamIndices, 0, bodyIndex, e.loc));
        
        // Create a scheme for the generic function and bind it to the environment
        const typeVars = e.typeParams.map(tvar);
        const paramTypes = e.params.map(() => newUnknown(builder)); // Unknown types for parameters
        const bodyType = newUnknown(builder); // Unknown type for body
        const funType = arrowN(paramTypes, bodyType);
        const scheme_ = builder.scheme(e.name, e.typeParams, funType);

        console.log("scheme for ", e.name, scheme_);
        
        // Store the scheme in the builder for later binding
        builder.schemes.set(scheme_.id, scheme_);
        
        return funDeclIndex;
      }

      case "TypeApp": {
        const ctorIndex = convertExpr(e.ctor);
        const argsIndices = e.args.map(convertExpr);
        return builder.addNode(nodeFac.typeApp(ctorIndex, argsIndices, e.loc));
      }

      default: {
        const _: never = e;
        assert(false, "Unexpected expression", { e });
      }
    }
  }
  
  const rootIndex = convertExpr(expr);
  builder.types = new Array(builder.nodes.length).fill(null);
  const program = new Program(builder.nodes, builder.types, rootIndex, builder.schemes, builder.apps, builder.instantiations);
  builder.program = program;
  return program;
}

/*======================================================================*/
/* 4.  Lineariser                                                       */
/*======================================================================*/

// Unified lineariseType function that handles both type parameters and type annotations
const lineariseType = (program: Program, code: Instr[], nodeIdx: number, loc: Loc) => {
  if (nodeIdx === -1) return code.push({op:"unknown", loc});
  
  const node = program.getNode(nodeIdx);
  
  if (node.kind === "Var") {
    code.push({op:"resolveTypeAnnotation",annotation:node.name,nodeIdx,loc:node.location});
    code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
  } else if (node.kind === "TypeApp") {
    node.typeArgsIndices.forEach(argIndex => {
      lineariseType(program, code, argIndex, node.location);
    });
    const baseNode = program.getNode(node.baseIndex);
    assert(baseNode.kind === "Var", "Expected var node for now", { baseNode });
    code.push({op:"applyT",name:baseNode.name,nodeIdx,arity:node.typeArgsIndices.length,loc:node.location});
    code.push({op:"storeType",nodeIdx:nodeIdx,loc:node.location});
  } else {
    assert(false, "Unexpected node kind for lineariseType", { node });
  }
};

// Modified lineariser to work with Program
function lineariseProgram(builder: ProgramBuilder, nodeIdx: number, mode: "synth" | "check" = "synth", expect?: Type): Instr[] {
  const program = builder.program;
  assert(program, "Program is required");

  const code: Instr[] = [];
  const node = program.getNode(nodeIdx);
  
  const synth = (index: number) => code.push(...lineariseProgram(builder, index, "synth"));
  const checkM = (index: number, t: Type) => code.push(
    {op:"pushExpect", ty: t, loc: node.location},
    ...lineariseProgram(builder, index, "synth"),
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
        scheme_ = builder.scheme(node.name, [], null!);
        program.schemes.set(scheme_.id, scheme_);

        for (const typeParamIndex of node.typeParamsIndices) {
          const typeParamNode = program.getNode(typeParamIndex);
          assert(typeParamNode.kind === "TypeParam", "Expected type param node for now");
          typeParams[typeParamNode.name] = tvar(typeParamNode.name);
          scheme_.vars.push(typeParamNode.name);
        }
        
        // Add type parameters to the scope so they can be looked up
        for (const [name, type] of Object.entries(typeParams)) {
          code.push({op:"bindType", name, ty: type, loc: node.location});
        }
      }

      // Handle parameters
      for (const paramIndex of node.paramsIndices) {
        const paramNode = program.getNode(paramIndex);
        if (paramNode.kind === "FunParam") {
          // For now, assume unannotated parameters get unknown types
          lineariseType(program, code, paramNode.typeIndex, paramNode.location);
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

        lineariseType(program, code, node.typeIndex, typeNode.location);
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
        synth(node.statementsIndices[i]!);
        code.push({op:"pop",loc:node.location});
      }
      code.push(...lineariseProgram(builder, node.statementsIndices[n-1]!, mode, expect));
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
  builder: ProgramBuilder; // Builder for accessing type inference state
}
const createInterpreterState = (code: Instr[], initialEnv: Env, builder: ProgramBuilder, program?: Program): InterpreterState => ({ 
  code, 
  pc: 0, 
  typeStk: [], 
  expectStk: [], 
  envStk: [initialEnv],
  program,
  builder
});


const getOverloadMatch = (alts: ArrowNType[], argTys: Type[], builder: ProgramBuilder): ArrowNType => {
  const arity = argTys.length;
  const exactMatches: ArrowNType[] = [];
  const allMatches: ArrowNType[] = [];
  alts.forEach(alt => {
    if (alt.params.length !== arity) return;
    
    // Check if all arguments match exactly without implicit casts
    let subtype = false;
    for (let j = 0; j < arity; j++) {
      if (!trySubsume(argTys[j]!, alt.params[j]!, builder)) return;
      if (isStrictSubtype(argTys[j]!, alt.params[j]!, builder)) subtype = true;
    }
    allMatches.push(alt);
    if (!subtype) exactMatches.push(alt);
  });
  
  // TODO: Better error messages
  assert(allMatches.length > 0, `no viable overloads for ${arity} arguments`, { arity, argTys, alts });

  if (exactMatches.length === 1) return exactMatches[0]!;
  if (exactMatches.length === 0 && allMatches.length === 1) return allMatches[0]!;
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
    const match = getOverloadMatch(fnTy.alts, argTys, state.builder);
    for (let j = 0; j < arity; j++) {
      subsume(argTys[j]!, match.params[j]!, true, state.builder).getOrThrow()
    }
    const res = resolve(match.result, state.builder);
    updateApp(state, nodeIdx, -1, match, argTys, res);
    return res;
  } else if (isArrowN(fnTy)) {
    assert(fnTy.params.length === arity, `function expects ${fnTy.params.length} arguments but got ${arity}`, { fnTy, arity });
    for (let j = 0; j < arity; j++) {
      subsume(argTys[j]!, fnTy.params[j]!, true, state.builder).getOrThrow()
    }
    const res = resolve(fnTy.result, state.builder);
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
    return arrowN(args.slice(0, -1), args[args.length - 1]!);
  }
    
  const e = state.envStk[state.envStk.length-1]?.get(name);
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

  const env = () => envStk[envStk.length-1]!;
  const envSetVal = (name: string, type: Type | Scheme) => env().set(name, { value: { tag:"KnownV", schemeOrType: type } });
  const envSetType = (name: string, type: Type | Scheme) => env().set(name, { type: { tag:"KnownT", schemeOrType: type } });

  const popN = (n: number): Type[] => {
    assert(n > 0, "popN: n must be positive");
    assert(n <= typeStk.length, "popN: n must be less than or equal to the stack length");
    return typeStk.splice(typeStk.length - n, n);
  };

  for (; state.pc < code.length; state.pc++) {
    const i = state.instr = code[state.pc]!;
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
      case "bindType": envSetType(i.name, i.ty); break;
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
        console.log(`Stored type ${show(topType, state.builder)} at node index ${i.nodeIdx}`);
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
        const fnTy   = resolve(typeStk.pop()!, state.builder);
        const res = applyN(state, i.nodeIdx, i.arity, fnTy, argTys);
        typeStk.push(res);
        break;
      }

      case "pushExpectFromStack": expectStk.push(typeStk[typeStk.length-1]!); break;
      case "pushExpect": expectStk.push(i.ty); break;
      case "popExpect":
        const got = typeStk[typeStk.length-1]!;
        const expect = expectStk.pop()!;
        const result = subsume(got, expect, false, state.builder);
        assert(result.ok, result.errorOrNull?.message ?? '', { result, got, expect });
        break;

      case "pop": typeStk.pop(); break;

      case "join": {
        const b = typeStk.pop()!;
        const a = typeStk.pop()!;
        unify(a,b, false, state.builder).getOrThrow();
        typeStk.push(resolve(a, state.builder));
        break;
      }

      case "applyT": {
        const argsTys = popN(i.arity);
        const res = lookupType(state, i.name, i.nodeIdx, i.loc, argsTys);
        typeStk.push(res);
        break;
      }

      case "unknown": {
        typeStk.push(newUnknown(state.builder));
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
    console.log("typeStk =", typeStk.map(t => show(t, state.builder)).join(", "));
    throw new Error("ill-typed program");
  }
  const res = resolve(typeStk[0]!, state.builder);
  console.log("type =", show(res, state.builder));
  
  // Discharge any deferred obligations after type solving is complete
  dischargeDeferredObligations(state);
  
  // Resolve all application data and instantiations after type solving is complete
  if (state.program) {
    for (const app of state.program.apps.values()) {
      app.fn = resolveRecursive(app.fn, state.builder);
      app.args = app.args.map(arg => resolveRecursive(arg, state.builder));
      app.result = resolveRecursive(app.result, state.builder);
    }
    
    // Also resolve instantiation data
    for (const inst of state.program.instantiations) {
      inst.args = inst.args.map(arg => resolveRecursive(arg, state.builder));
      inst.mono = resolveRecursive(inst.mono, state.builder);
    }
  }
  
  return res;
}

const locStr = (i:Instr) => `${i.loc.file}:${i.loc.line}:${i.loc.col}`;
const compactInspect = (i: any) => inspect(i, { depth: 1, colors: true, compact: true })

// Export missing types and functions for tests
export type { Instr, Env, Expr, RunResult, InterpreterState, SuspendMissing };
export { 
  assert, 
  isType, 
  isScheme,
  newUnknown, 
  arrow, 
  arrowN, 
  int, 
  bool, 
  v, 
  lam, 
  lamN,
  app, 
  appN,
  _if, 
  _let, 
  block,
  exprToProgram,
  lineariseProgram,
  lineariseType,
  runInternal,
  createInterpreterState,
  startTrial,
  rollback,
  commit,
  unify,
  subsume,
  show,
  resolveRecursive,
  tvar,
  tapp,
  tstruct,
  overload,
  scheme,
  dummy,
  getNextSchemeId,
  isArrowN,
  compactInspect,
  funDecl,
  typeApp,
  areTypesEqual,
  // Type constraints system exports
  typeKey,
  requireTraitNow,
  dischargeDeferredObligations,
  emitObligationsForInstantiation,
  tryCheckOrDefer,
  substWalk,
  containsUnknown,
  canonicalKey,
  fail,
  registerTrait,
  registerTraitImpl,
  createBounds
};
