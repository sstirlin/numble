import strutils
import math
import macros
import sequtils
import unittest
import typetraits


{.experimental.}  # for automatic dereferencing


type

  StridedArrayObj*[T] = object of RootObj

    shape*: seq[int]
    ndim*: int
    size*: int
    strides*: seq[int]
    offset*: int
    data*: seq[T]
    mask*: StridedArray[bool]


  StridedArray*[T] = ref object of StridedArrayObj[T]


proc newNilStridedArray[T](shape: openarray[int]): StridedArray[T] =

  new result
  result.data = nil
  result.mask = nil
  result.shape = @shape
  result.ndim = len(shape)
  result.size = 1
  for i in result.shape:
    if i < 1:
      raise newException(RangeError, "StridedArray shape must be list of integers > 0")
    result.size *= i

  result.strides = newSeq[int](result.ndim)
  result.strides[result.ndim-1] = 1
  for i in countdown(result.ndim-1, 1):
    result.strides[i-1] = result.strides[i]*shape[i]

  result.offset = 0


proc empty*[T](shape: openarray[int]): StridedArray[T] =

  result = newNilStridedArray[T](shape)
  result.data = newSeq[T](result.size)


proc stridedView*[T](data: seq[T], shape: openarray[int]): StridedArray[T] =

  result = newNilStridedArray[T](shape)
  if result.size > len(data):
    raise newException(RangeError, "StridedArray shape is larger than provided buffer")

  shallowCopy(result.data, data)


proc rawIx*[T](arr: StridedArray[T], ix: seq[int]): int {.inline.} =

  var args = ix # mutable copy

  when compileOption("boundChecks"):
    if len(args) != arr.ndim:
      raise newException(IndexError, "StridedArray index must match shape")

  result = arr.offset
  for i in 0.. <len(args):
    when compileOption("boundChecks"):
      if args[i] >= arr.shape[i] or args[i] < -arr.shape[i]:
        raise newException(IndexError, "StridedArray index is out of bounds")
    if args[i] < 0:
      args[i] += arr.shape[i]
    result += args[i] * arr.strides[i]


proc rawIx*[T](arr: StridedArray[T], ix: varargs[int]): int {.inline.} =

  var args = @ix # mutable copy

  when compileOption("boundChecks"):
    if len(args) != arr.ndim:
      raise newException(IndexError, "StridedArray index must match shape")

  result = arr.offset
  for i in 0.. <len(args):
    when compileOption("boundChecks"):
      if args[i] >= arr.shape[i] or args[i] < -arr.shape[i]:
        raise newException(IndexError, "StridedArray index is out of bounds")
    if args[i] < 0:
      args[i] += arr.shape[i]
    result += args[i] * arr.strides[i]


iterator indices[T](arr: StridedArray[T]): seq[int] =

  if isNil(arr.mask):
    var ix = newSeq[int](arr.ndim)
    for dim in 0.. <arr.ndim:
      ix[dim]=0
    for i in 0.. <arr.size:
      yield ix
      for dim in countdown(arr.ndim-1,0):
        ix[dim] += 1
        if ix[dim] == arr.shape[dim]:
          ix[dim] = 0
        else:
          break

  else:
    var ix = newSeq[int](arr.ndim)
    for dim in 0.. <arr.ndim:
      ix[dim]=0
    for i in 0.. <arr.size:
      if arr.mask[ix]:
        yield ix
      for dim in countdown(arr.ndim-1,0):
        ix[dim] += 1
        if ix[dim] == arr.shape[dim]:
          ix[dim] = 0
        else:
          break


iterator flat[T](arr: StridedArray[T]): int =

  if isNil(arr.mask):
    var ix = newSeq[int](arr.ndim)
    for dim in 0.. <arr.ndim:
      ix[dim]=0
    for i in 0.. <arr.size:
      yield arr.rawIx(ix)
      for dim in countdown(arr.ndim-1,0):
        ix[dim] += 1
        if ix[dim] == arr.shape[dim]:
          ix[dim] = 0
        else:
          break

  else:
    var ix = newSeq[int](arr.ndim)
    for dim in 0.. <arr.ndim:
      ix[dim]=0
    for i in 0.. <arr.size:
      if arr.mask[ix]:
        yield arr.rawIx(ix)
      for dim in countdown(arr.ndim-1,0):
        ix[dim] += 1
        if ix[dim] == arr.shape[dim]:
          ix[dim] = 0
        else:
          break


proc equal[T](arr1: StridedArray[T], arr2: StridedArray[T]): bool =

  if isNil(arr1):
    if isNil(arr2):
      return true
    else:
      return false

  if isNil(arr2):
    return false

  if arr1.shape != arr2.shape:
    return false
  if arr1.ndim != arr2.ndim:
    return false
  if arr1.size != arr2.size:
    return false
  if arr1.strides != arr2.strides:
    return false
  if arr1.offset != arr2.offset:
    return false
  
  for ix in arr1.indices:
    if arr1[ix] != arr2[ix]:
      return false

  if not equal(arr1.mask, arr2.mask):
    return false

  return true


proc shallowCopy*[T](arr: StridedArray[T]): StridedArray[T] =

  # strings and seqs are technically ref types, but they have
  # special behavior:  `=` copies them deeply
  # for other ref types, `=` is shallow
  new result
  result.shape = arr.shape  # deep
  result.ndim = arr.ndim  # deep
  result.size = arr.size  # deep
  result.strides = arr.strides  # deep
  result.offset = arr.offset  # deep
  shallowCopy(result.data, arr.data)  # explicitly shallow
  result.mask = arr.mask  # shallow (since StridedArray is a ref type)


proc deepCopy*[T](arr: StridedArray[T]): StridedArray[T] =

  if isNil(arr):
    return nil

  result = empty[T](arr.shape)
  for ix in arr.indices:
    result[ix] = arr[ix]

  result.mask = arr.mask.deepCopy


proc emptyLike*[T](arr: StridedArray[T]): StridedArray[T] =

  if isNil(arr):
    return nil

  result = empty[T](arr.shape)
  result.mask = arr.mask.deepCopy


template `[]`*[T](arr: StridedArray[T], ix: varargs[int]): expr =

  arr.data[arr.rawIx(ix)]


template `[]`*[T](arr: StridedArray[T], ix: seq[int]): expr =

  arr.data[arr.rawIx(ix)]


proc `[]=`*[T](arr: var StridedArray[T], ix: varargs[int], rhs: T) =

  arr.data[arr.rawIx(ix)] = rhs


proc `[]=`*[T](arr: var StridedArray[T], ix: seq[int], rhs: T) =

  arr.data[arr.rawIx(ix)] = rhs


const _ = high(int)
    

macro `[]`[T](arr: StridedArray[T], e: string): expr =

  var args = split(e.strVal, ",")
  var code = $arr & "["

  for i in 0.. <len(args):
    if strip(args[i]) == "...":
      code.add("all")
    else:
      var ixs = split(strip(args[i]), ":")
      if len(ixs) == 0 or len(ixs) > 3:
        error("StridedArray slice index is invalid")
      elif len(ixs) == 1:
        code.add(ixs[0])
      elif len(ixs) > 1:
        # if first index is empty, fill in default
        if strip(ixs[0]) == "":
          ixs[0] = $_
        # if second index is empty, fill in default
        if strip(ixs[1]) == "":
          ixs[1] = $_
        # if step if missing, fill in default
        if len(ixs) < 3:
          ixs.add("1")
        elif strip(ixs[2]) == "":
          ixs[2] = "1"
        
        # convert from pythonic [,) to nimlike [,] intervals
        # by adding or subtracting 1 (depending on the sign of "step")
        if ixs[1] != $_:  # NOTE: leave alone if default value
          ixs[1].add("-(")
          ixs[1].add(ixs[2])
          ixs[1].add(")/abs(")
          ixs[1].add(ixs[2])
          ixs[1].add(")")

        code.add("int(")
        code.add(ixs[0])
        code.add(")")
        code.add("..")
        code.add("int(")
        code.add(ixs[1])
        code.add(")")
        code.add("|")
        code.add("int(")
        code.add(ixs[2])
        code.add(")")
    if i != len(args)-1:
      code.add(",")

  code.add("]")
  parseExpr(code)


type

  SteppedSlice*[T] = object of RootObj
    a*, b*: T
    step*: T


proc initSteppedSlice*[T](a, b, step: T): SteppedSlice[T] =

  result.a = a
  result.b = b
  result.step = step


# need an iterator so that SteppedSlice can be used in for loops (just like Slice)

iterator items*[T](s: SteppedSlice[T]): T =

  if s.a <= s.b:
    for val in countup(s.a, s.b, s.step):
      yield val
  else:
    for val in countdown(s.a, s.b, -s.step):  # countdown expects positive step
      yield val


# This might be stupid.  Overriding `..` family of operators to return SteppedSlice instead of Slice

proc `..`*[T](a, b: T): SteppedSlice[T] =

  result.a = a
  result.b = b
  result.step = 1


proc `..+`*[T](a, b: T): SteppedSlice[T] =

  result.a = a
  result.b = b
  result.step = 1


proc `..-`*[T](a, b: T): SteppedSlice[T] =

  result.a = a
  result.b = -b
  result.step = 1


# We need these because, when we write
#   a..b|step
#
# The compiler sees this
#   a..(b|step)
#
# not this
#   (a..b)|step
#
# See the comments about `|` below


proc `..`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = a
  result.b = s.b
  result.step = s.step


proc `..+`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = a
  result.b = s.b
  result.step = s.step


proc `..-`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = a
  result.b = -s.b
  result.step = s.step


# Support for `..<` style syntax

# THIS IS NOW REWRITTEN TO ".. <" BY THE STANDARD LIB
#proc `..<`*[T](a, b: T): SteppedSlice[T] =
#
#  result.a = a
#  result.b = pred(b)
#  result.step = 1


proc `..<-`*[T](a, b: T): SteppedSlice[T] =

  result.a = a
  result.b = pred(-b)
  result.step = 1


proc `..<+`*[T](a, b: T): SteppedSlice[T] =

  result.a = a
  result.b = pred(b)
  result.step = 1


# We need these because, when we write
#   a..<b|step
#
# The compiler sees this
#   a..<(b|step)
#
# not this
#   (a..<b)|step
#
# See the comments about `|` below

# THIS IS NOW REWRITTEN TO ".. <" BY THE STANDARD LIB
#proc `..<`*[T](a: T, s: SteppedSlice): SteppedSlice[T] =
#
#  result.a = a
#  result.b = pred(s.b)
#  result.step = s.step


proc `..<-`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = a
  result.b = pred(-s.b)
  result.step = s.step


proc `..<+`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = a
  result.b = pred(s.b)
  result.step = s.step


# UnaryLt operators (necessary because system.nim rewrites `..<` as `.. <`)

proc `<`*[T](s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = s.a
  result.b = pred(s.b)
  result.step = s.step


proc `<-`*[T](s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = s.a
  result.b = pred(-s.b)
  result.step = s.step


proc `<+`*[T](s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = s.a
  result.b = pred(s.b)
  result.step = s.step


# Backfill UnaryLt operators missing from system.nim

# already supplied in system.nim
#proc `<`*[T](a: T): T =
#
#  result = pred(a)

proc `<-`*[T](a: T): T =

  result = pred(-a)


proc `<+`*[T](a: T): T =

  result = pred(a)


# Since `|` is a high-precedence operator, in an expression
# like this:
#   a..b|step
#
# The compiler actually sees this
#   a..(b|step)
#
# not this
#   (a..b)|step

proc `|`*[T](b, step: T): SteppedSlice[T] =

  result.a = _
  result.b = b
  result.step = step


proc `|-`*[T](b, step: T): SteppedSlice[T] =

  result.a = _
  result.b = b
  result.step = -step


proc `|+`*[T](b, step: T): SteppedSlice[T] =

  result.a = _
  result.b = b
  result.step = step


# these are probably unnecessary because `|` is a high-precedence operator
# See the commentary above

proc `|`*[T](s: SteppedSlice[T], step: T): SteppedSlice[T] =

  result.a = s.a
  result.b = s.b
  result.step = step


proc `|-`*[T](s: SteppedSlice[T], step: T): SteppedSlice[T] =

  result.a = s.a
  result.b = s.b
  result.step = -step


proc `|+`*[T](s: SteppedSlice[T], step: T): SteppedSlice[T] =

  result.a = s.a
  result.b = s.b
  result.step = step


# support for syntax like `>..`

proc `>..`*[T](a, b: T): SteppedSlice[T] =

  result.a = pred(a)
  result.b = b
  result.step = 1


proc `>..-`*[T](a, b: T): SteppedSlice[T] =

  result.a = pred(a)
  result.b = -b
  result.step = 1


proc `>..+`*[T](a, b: T): SteppedSlice[T] =

  result.a = pred(a)
  result.b = b
  result.step = 1


proc `>..`*[T](a: T, s: SteppedSlice): SteppedSlice[T] =

  result.a = pred(a)
  result.b = s.b
  result.step = s.step


proc `>..-`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = pred(a)
  result.b = -s.b
  result.step = s.step


proc `>..+`*[T](a: T, s: SteppedSlice[T]): SteppedSlice[T] =

  result.a = pred(a)
  result.b = s.b
  result.step = s.step


# unary creation operators (a=default, b=default)

proc `..|`*[T](step: T): SteppedSlice[T] =

  result.a = _
  result.b = _
  result.step = step


proc `..|-`*[T](step: T): SteppedSlice[T] =

  result.a = _
  result.b = _
  result.step = -step


proc `..|+`*[T](step: T): SteppedSlice[T] =

  result.a = _
  result.b = _
  result.step = step


let all = initSteppedSlice[int](0,0,0)


proc `[]`*[T](arr: StridedArray[T], ix: varargs[SteppedSlice[int]]): StridedArray[T] =

  var args = newSeq[SteppedSlice[int]](0)
  
  # If 'all' specified in front or back then expand it
  if ix[0] == all:
    for i in 1.. <len(ix):
      if ix[i] == all:
        raise newException(IndexError, "'all' is only allowed either at the front or back of an StridedArray, and never at the same time")
    for i in 1..(arr.ndim-(len(ix)-1)):
      args.add(..|1)
    for i in 1.. <len(ix):
      args.add(ix[i])
  elif ix[len(ix)-1] == all:
    for i in 0.. <(len(ix)-1):
      if ix[i] == all:
        raise newException(IndexError, "'all' is only allowed either at the front or back of an StridedArray, and never at the same time")
    for i in 0.. <(len(ix)-1):
      args.add(ix[i])
    for i in 1..(arr.ndim-(len(ix)-1)):
      args.add(..|1)
  else:
    for i in 0.. <len(ix):
      args.add(ix[i])

  if len(args) != arr.ndim:
    raise newException(IndexError, "new StridedArray must have same shape as original")

  result = arr.shallowCopy

  # first check that ranges make sense
  for i in 0..(len(args)-1):
      
    if args[i].step < 0:
      if args[i].b == _:
        args[i].b = 0
      if args[i].a == _:
        args[i].a = arr.shape[i]-1 
    else:
      if args[i].b == _:
        args[i].b = arr.shape[i]-1 
      if args[i].a == _:
        args[i].a = 0

    if args[i].a >= arr.shape[i] or args[i].a < -arr.shape[i]:
      raise newException(IndexError, "StridedArray index is out of bounds")
    if args[i].b >= arr.shape[i] or args[i].b < -arr.shape[i]:
      raise newException(IndexError, "StridedArray index is out of bounds")
    if args[i].a < 0:
      args[i].a += arr.shape[i]
    if args[i].b < 0:
      args[i].b += arr.shape[i]
    args[i].b -= (args[i].b - args[i].a) mod args[i].step  # make array bounds evenly divisible by stepsize
    if (args[i].b - args[i].a) div args[i].step < 0:
      raise newException(IndexError, "StridedArray must have range in same direction as step")

  # set offset
  for i, v in args:
    result.offset += v.a * result.strides[i]

  # set shape and strides    
  result.size = 1
  for i, v in args:
    result.strides[i] *= v.step
    result.shape[i] = abs((v.b - v.a) div v.step) + 1
    result.size *= result.shape[i]


proc `[]`*[T](arr: StridedArray[T], mask: StridedArray[bool]): StridedArray[T] =

  if mask.shape != arr.shape:
    raise newException(RangeError, "boolean mask must have same shape as StridedArray")

  result = arr.shallowCopy
  result.mask = mask.shallowCopy


proc `[]=`*[T](arr: var StridedArray[T], mask: StridedArray[bool], rhs: StridedArray[T]) =

  if arr.shape != rhs.shape:
    raise newException(RangeError, "lhs must have same shape as rhs")

  if mask.shape != arr.shape:
    raise newException(RangeError, "boolean mask must have same shape as StridedArray")
  
  if isNil(rhs.mask):
    raise newException(RangeError, "rhs must be masked")

  for ix in mask.indices:
    if mask[ix] != rhs.mask[ix]:
      raise newException(RangeError, "rhs mask must match lhs mask")

  for ix in rhs.indices:
    arr.data[arr.rawIx(ix)] = rhs.data[rhs.rawIx(ix)]


proc fill*[T](arr: var StridedArray[T], val: T) =

  for ix in arr.indices:
    arr[ix] = val


macro vectorizeBinOpArrScalarT*(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: StridedArray[$2], s: $2): StridedArray[$3] =

               result = empty[$3](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2](arr[ix], s) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


macro vectorizeBinOpScalarArrT*(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](s: $2, arr: StridedArray[$2]): StridedArray[$3] =

               result = empty[$3](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2](s, arr[ix]) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


macro vectorizeBinOpArrArrT*(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: StridedArray[$2], s: StridedArray[$2]): StridedArray[$3] =

               if arr.shape != s.shape:
                 raise newException(RangeError, "StridedArrays must have same shape")

               if not equal(arr.mask, s.mask):
                 raise newException(RangeError, "StridedArrays must be masked the same")

               result = empty[$3](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2](arr[ix], s[ix]) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


template vectorizeBinOpT*(op, T, Tout: expr): stmt {.immediate.} =

  vectorizeBinOpArrScalarT(op, T, Tout)
  vectorizeBinOpScalarArrT(op, T, Tout)
  vectorizeBinOpArrArrT(op, T, Tout)


macro vectorizeBinOpArrTScalarS*(op, T, S, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2, $3](arr: StridedArray[$2], s: $3): StridedArray[$4] =

               result = empty[$4](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2, $3](arr[ix], s) 
             """ % [opstr, $T, $S, $Tout]
  result = parseStmt(body)


macro vectorizeBinOpScalarSArrT*(op, S, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2, $3](s: $2, arr: StridedArray[$3]): StridedArray[$4] =

               result = empty[$4](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2, $3](s, arr[ix]) 
             """ % [opstr, $S, $T, $Tout]
  result = parseStmt(body)


macro vectorizeBinOpArrTArrS*(op, T, S, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2, $3](arr: StridedArray[$2], s: StridedArray[$3]): StridedArray[$4] =

               if arr.shape != s.shape:
                 raise newException(RangeError, "StridedArrays must have same shape")

               if not equal(arr.mask, s.mask):
                 raise newException(RangeError, "StridedArrays must be masked the same")

               result = empty[$4](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2, $3](arr[ix], s[ix]) 
             """ % [opstr, $T, $S, $Tout]
  result = parseStmt(body)


template vectorizeBinOpTS*(op, T, S, Tout: expr): stmt {.immediate.} =

  vectorizeBinOpArrTScalarS(op, T, S, Tout)
  vectorizeBinOpScalarSArrT(op, S, T, Tout)
  vectorizeBinOpArrTArrS(op, T, S, Tout)


macro vectorizeInplaceOpArrScalarT*(op, T: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: var StridedArray[$2], s: $2) =

               for ix in arr.indices:
                 $1(arr[ix], s) 
             """ % [opstr, $T]
  result = parseStmt(body)


macro vectorizeInplaceOpArrArrT*(op, T: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: var StridedArray[$2], s: StridedArray[$2]) =

               if arr.shape != s.shape:
                 raise newException(RangeError, "StridedArrays must have same shape")

               if not equal(arr.mask, s.mask):
                 raise newException(RangeError, "StridedArrays must be masked the same")

               for ix in arr.indices:
                 $1(arr[ix], s[ix]) 
             """ % [opstr, $T]
  result = parseStmt(body)


template vectorizeInplaceOpT*(op, T: expr): stmt {.immediate.} =

  vectorizeInplaceOpArrScalarT(op, T)
  vectorizeInplaceOpArrArrT(op, T)


macro vectorizeUnaryOpArrT*(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: StridedArray[$2]): StridedArray[$3] =

               result = empty[$3](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1[$2](arr[ix]) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


macro vectorizeTypeConversion*(totype, T: expr): stmt {.immediate.} =

  let body = """
             proc to$1*[$2](arr: StridedArray[$2]): StridedArray[$1] =

               result = empty[$1](arr.shape)
               result.mask = arr.mask
               for ix in arr.indices:
                 result[ix] = $1(arr[ix]) 
             """ % [$totype, $T]
  result = parseStmt(body)


vectorizeBinOpT(`==`, T, bool)
vectorizeBinOpT(`!=`, T, bool)
vectorizeBinOpT(`<`, T, bool)
vectorizeBinOpT(`<=`, T, bool)
vectorizeBinOpT(`>`, T, bool)
vectorizeBinOpT(`>=`, T, bool)

vectorizeBinOpT(`==%`, T, bool)
vectorizeBinOpT(`<%`, T, bool)
vectorizeBinOpT(`<=%`, T, bool)
vectorizeBinOpT(`>%`, T, bool)
vectorizeBinOpT(`>=%`, T, bool)

vectorizeBinOpT(`+`, T, T)
vectorizeBinOpT(`-`, T, T)
vectorizeBinOpT(`*`, T, T)
vectorizeBinOpT(`/`, T, T)

vectorizeBinOpT(`+%`, T, T)
vectorizeBinOpT(`-%`, T, T)
vectorizeBinOpT(`*%`, T, T)
vectorizeBinOpT(`/%`, T, T)
vectorizeBinOpT(`%%`, T, T)

vectorizeBinOpT(`div`, T, T)
vectorizeBinOpT(`mod`, T, T)
vectorizeBinOpT(`shr`, T, T)
vectorizeBinOpT(`shl`, T, T)
vectorizeBinOpT(`and`, T, T)
vectorizeBinOpT(`or`, T, T)
vectorizeBinOpT(`xor`, T, T)
vectorizeBinOpT(cmp, T, T)
vectorizeBinOpT(`&`, string, string)
vectorizeBinOpT(binom, int, int)
vectorizeBinOpT(arctan2, float, float)
vectorizeBinOpT(hypot, float, float)
vectorizeBinOpT(pow, float, float)
vectorizeBinOpT(fmod, float, float)
vectorizeBinOpT(`^`, T, T)
vectorizeBinOpT(gcd, T, T)
vectorizeBinOpT(lcm, T, T)


vectorizeInplaceOpT(add, string)
vectorizeInplaceOpT(`+=`, T)
vectorizeInplaceOpT(`-=`, T)
vectorizeInplaceOpT(`*=`, T)
vectorizeInplaceOpT(`/=`, T)
vectorizeInplaceOpT(`&=`, string)


vectorizeUnaryOpArrT(`not`, T, T)
vectorizeUnaryOpArrT(fac, int, int)
vectorizeUnaryOpArrT(sqrt, float, float)
vectorizeUnaryOpArrT(ln, float, float)
vectorizeUnaryOpArrT(log10, float, float)
vectorizeUnaryOpArrT(exp, float, float)
vectorizeUnaryOpArrT(round, float, float)
vectorizeUnaryOpArrT(arccos, float, float)
vectorizeUnaryOpArrT(arcsin, float, float)
vectorizeUnaryOpArrT(arctan, float, float)
vectorizeUnaryOpArrT(cos, float, float)
vectorizeUnaryOpArrT(cosh, float, float)
vectorizeUnaryOpArrT(sin, float, float)
vectorizeUnaryOpArrT(sinh, float, float)
vectorizeUnaryOpArrT(tan, float, float)
vectorizeUnaryOpArrT(tanh, float, float)
vectorizeUnaryOpArrT(random, T, T)
vectorizeUnaryOpArrT(trunc, float, float)
vectorizeUnaryOpArrT(floor, float, float)
vectorizeUnaryOpArrT(ceil, float, float)


# generates toInt, toFloat, toFloat32, etc.
vectorizeTypeConversion(int, T)
vectorizeTypeConversion(int8, T)
vectorizeTypeConversion(int16, T)
vectorizeTypeConversion(int32, T)
vectorizeTypeConversion(int64, T)
vectorizeTypeConversion(uint, T)
vectorizeTypeConversion(uint8, T)
vectorizeTypeConversion(uint16, T)
vectorizeTypeConversion(uint32, T)
vectorizeTypeConversion(uint64, T)
vectorizeTypeConversion(float, T)
vectorizeTypeConversion(float32, T)
vectorizeTypeConversion(float64, T)


when isMainModule:

  test "Can create empty StridedArray of specific shape and fill it with a value":
    var arr = empty[float]([3,4,3])
    arr.fill(5.0)
    for ix in arr.indices:
      check arr[ix] == 5.0

  # or we can attach to a raw sequence
  # using the "stridedView" proc
  var raw = newSeq[int](36)
  for i in 0..35:
      raw[i] = i

  test "Size bigger than than underlying raw buffer throws RangeError":
    expect RangeError:
      discard stridedView(raw, [3,4,4])

  test "Nonsensical shape throws RangeError":
    expect RangeError:
      discard stridedView(raw, [-3,4,3])
    expect RangeError:
      discard stridedView(raw, [3,-4,3])
    expect RangeError:
      discard stridedView(raw, [3,4,-3])
    expect RangeError:
      discard stridedView(raw, [3,-4,-3])
    expect RangeError:
      discard stridedView(raw, [-3,-4,-3])


  var arr = stridedView(raw, [3,4,3])

  test "Shape, size, ndim, strides, offset, data, are correct":
    check arr.shape == @[3,4,3]
    check arr.size == 36
    check arr.ndim == 3
    check arr.strides == @[12,3,1]
    check arr.offset == 0
    check arr.data == raw
  
  test "`=` gives another reference to the same object":
    var oldval = arr[0,0,0]
    var arrshallow = arr
    check arrshallow[0,0,0] == oldval
    arr[0,0,0] = high(int)
    check arrshallow[0,0,0] == high(int)
    arr[0,0,0] = oldval

  test "Invalid index shape throws IndexError":
    expect IndexError:
      discard arr[0,0,0,0]
    expect IndexError:
      discard arr[0,0]
    expect IndexError:
      arr[0,0,0,0] = 0
    expect IndexError:
      arr[0,0] = 0

  test "Out-of-bounds indexing throws IndexError":
    expect IndexError:
      discard arr[3,0,0]
    expect IndexError:
      discard arr[0,4,0]
    expect IndexError:
      discard arr[0,0,3]
    expect IndexError:
      discard arr[-4,0,0]
    expect IndexError:
      discard arr[0,-5,0]
    expect IndexError:
      discard arr[0,0,-4]

  test "Iterating through the array returns expected values":
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          #echo "arr[$#,$#,$#]= "%[$i,$j,$k] & $arr[i,j,k]
          check arr[i,j,k] == k + 3*j + 12*i

  test "Iterating using negative indices is the same as iterating in reverse":
    for i in countdown(-1,-3):
      for j in countdown(-1,-4):
        for k in countdown(-1,-3):
          check arr[i,j,k] == (3+k) + 3*(4+j) + 12*(3+i)

  test "Assignment works for both positive and negative indices (let's reverse the underlying data)":
    for i in 0..2:
      for j in 0..3:
        for k in j..2:
          var temp = arr[i,j,k]
          arr[i,j,k] = arr[-i-1,-j-1,-k-1]
          arr[-i-1,-j-1,-k-1] = temp

  test "The underlying data is now reversed":
    for i in 0..35:
      check arr.data[i] == 35-i

  test "We can \"reverse\" the array back to normal by using a strided view (note: endpoints are *inclusive*)":
    var revarr = arr[2..0|-1, 3..0|-1, 2..0|-1]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == k + 3*j + 12*i

  test "Notation like `..|1` also works if we desire the full range":
    var revarr = arr[..|-1, ..|-1, ..|-1]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == k + 3*j + 12*i

  test "The symbol `_` can be substituted for any endpoint as well":
    var revarr = arr[_..0|-1, 3.._|-1, _.._|-1]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == k + 3*j + 12*i

  test "..< syntax works":
    var arr2 = arr[0..<arr.shape[0], 0..<arr.shape[1], 0..<arr.shape[2]]
    for i in arr2.flat:
      check arr2.data[i] == arr.data[i]

  test "..< with step | syntax works":
    var arr2 = arr[0..<arr.shape[0]|1, 0..<arr.shape[1]|1, 0..<arr.shape[2]|1]
    for i in arr2.flat:
      check arr2.data[i] == arr.data[i]

  test ">.. syntax works":
    var revarr = arr[arr.shape[0]>..0|-1, arr.shape[1]>..0|-1, arr.shape[2]>..0|-1]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == k + 3*j + 12*i

  test "we haven't ruined the syntax ..< for ordinary use":
    var count = 0
    for i in 0..<100:
      check i == count
      count += 1 
    count = 0
    for i in 0.. <100:  # notice the space!
      check i == count
      count += 1 
    count = 0
    for i in 0..<100|2:  # now supports step sizes!
      check i == count
      count += 2 
    count = 99 
    for i in 100>..0|-2:  # counting backwards works
      check i == count
      count -= 2

  test "Pythonic `a:b:step` syntax can be passed as a string (`b` is *excluded*)":
    var revarr = arr["2:-1:-1, 3:-1:-1, 2:-1:-1"]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == k + 3*j + 12*i

  test "Pythonic `::step` syntax also works":
    var revarr = arr["::-1, ::-1, ::-1"]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == k + 3*j + 12*i

  test "More Pythonic shorthand works, e.g. `::`, `:`, `...`":
    var arr1 = arr["::, ::, ::"]
    var arr2 = arr[":, :, :"]
    var arr3 = arr["..., :, :"]
    var arr4 = arr[":, :, ..."]
    var arr5 = arr["..."]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check arr1[i,j,k] == 35 - (k + 3*j + 12*i)
          check arr2[i,j,k] == 35 - (k + 3*j + 12*i)
          check arr3[i,j,k] == 35 - (k + 3*j + 12*i)
          check arr4[i,j,k] == 35 - (k + 3*j + 12*i)
          check arr5[i,j,k] == 35 - (k + 3*j + 12*i)

  test "A view does not change the underlying data - it is still reversed":
    var revarr = arr[..|-1, ..|-1, ..|-1]
    for i in 0..<revarr.size:
      check revarr.data[i] == 35 - i

  test "A view is shallow - it shares the same underlying buffer":
    var revarr = arr[..|-1, ..|-1, ..|-1]
    revarr[0,0,0] = 123456
    check arr[2,3,2] == 123456
    revarr[0,0,0] = 0


  arr = arr[..|-1, ..|-1, ..|-1]


  test "Shape, size, ndim, strides, offset, are correct":
    check arr.shape == @[3,4,3]
    check arr.size == 36
    check arr.ndim == 3
    check arr.strides == @[-12,-3,-1]
    check arr.offset == 35

  test "\"all\" is used like \"...\" is used in Python":
    var arr1 = arr[all]
    for ix in arr1.indices:
      check arr1[ix] == arr[ix]
    var arr2 = arr[all, ..|1]
    for ix in arr2.indices:
      check arr2[ix] == arr[ix]
    var arr3 = arr[..|1, all]
    for ix in arr3.indices:
      check arr3[ix] == arr[ix]

  test "A view of a view works - let's reverse the last index again":
    var revarr = arr[..|1, ..|1, ..|-1]
    for i in 0..2:
      for j in 0..3:
        for k in 0..2:
          check revarr[i,j,k] == (2-k) + 3*j + 12*i

  test "Shape, size, ndim, strides, offset, are correct":
    var revarr = arr[..|1, ..|1, ..|-1]
    check revarr.shape == @[3,4,3]
    check revarr.size == 36
    check revarr.ndim == 3
    check revarr.strides == @[-12,-3,1]
    check revarr.offset == 33
  
  test "Shallow views can have stepsizes other than 1":
    var subarr = arr[..|2, ..|1, ..|1]
    for i in 0..1:  # notice how this index now goes from 0 to 1
      for j in 0..3:
        for k in 0..2:
          check subarr[i,j,k] == k + 3*j + 12*2*i

  test "Shape, size, ndim, strides, offset, are correct":
    var subarr = arr[..|2, ..|1, ..|1]
    check subarr.shape == @[2,4,3]
    check subarr.size == 24 
    check subarr.ndim == 3
    check subarr.strides == @[-24,-3,-1]
    check subarr.offset == 35

  test "We can have sub-subviews":
    var subarr = arr[..|2, ..|1, ..|1]
    var subsubarr = subarr[..|1, ..|2, ..|1]
    for i in 0..1:  # notice how this index now goes from 0 to 1
      for j in 0..1: # notice how this index now goes from 0 to 1 (the stepsize does not end exactly on the endpoint)
        for k in 0..2:
          check subsubarr[i,j,k] == k + 3*2*j + 12*2*i
    
  test "Shape, size, ndim, strides, offset, are correct":
    var subarr = arr[..|2, ..|2, ..|1]
    check subarr.shape == @[2,2,3]
    check subarr.size == 12 
    check subarr.ndim == 3
    check subarr.strides == @[-24,-6,-1]
    check subarr.offset == 35

  test "\"indices\" returns an iterator":
    var subarr = arr[..|2, ..|2, ..|2]
    var truth = @[0,2,6,8,24,26,30,32]
    var i = 0
    for ix in subarr.indices:
      check subarr[ix] == truth[i]
      i += 1

  test "\"flat\" returns an iterator to raw data":
    var subarr = arr[..|2, ..|2, ..|2]
    var truth = @[0,2,6,8,24,26,30,32]
    var i = 0
    for ix in subarr.flat:
     check subarr.data[ix] == truth[i]
     i += 1

  test "== works":

    # arr == scalar
    var boolmask = arr == 5
    for i in arr.indices:
      if arr[i] == 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar == arr
    boolmask = 5 == arr
    for i in arr.indices:
      if arr[i] == 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr == arr
    var allfives = emptyLike(arr)
    allfives.fill(5)

    boolmask = arr == allfives
    for i in arr.indices:
      if arr[i] == 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test "`or` works":

    # arr == scalar
    var boolmask = arr == 5 or arr == 6
    for i in arr.indices:
      if arr[i] == 5 or arr[i] == 6:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar == arr
    boolmask = 5 == arr or 6 == arr
    for i in arr.indices:
      if arr[i] == 5 or arr[i] == 6:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr == arr
    var allfives = emptyLike(arr)
    allfives.fill(5)
    var allsixes = emptyLike(arr)
    allsixes.fill(6)

    boolmask = arr == allfives or arr == allsixes
    for i in arr.indices:
      if arr[i] == 5 or arr[i] == 6:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test "`and` works":

    # arr == scalar
    var boolmask = arr == 5 and arr == 6
    for i in arr.indices:
      if arr[i] == 5 and arr[i] == 6:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar == arr
    boolmask = 5 == arr and 6 == arr
    for i in arr.indices:
      if arr[i] == 5 and arr[i] == 6:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr == arr
    var allfives = emptyLike(arr)
    allfives.fill(5)
    var allsixes = emptyLike(arr)
    allsixes.fill(6)

    boolmask = arr == allfives and arr == allsixes
    for i in arr.indices:
      if arr[i] == 5 and arr[i] == 6:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test "< works":

    # arr < scalar
    var boolmask = arr < 5
    for i in arr.indices:
      if arr[i] < 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar < arr
    boolmask = 5 < arr
    for i in arr.indices:
      if arr[i] > 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr == arr
    var allfives = emptyLike(arr)
    allfives.fill(5)

    boolmask = arr < allfives
    for i in arr.indices:
      if arr[i] < 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test "<= works":

    # arr <= scalar
    var boolmask = arr <= 5
    for i in arr.indices:
      if arr[i] <= 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar <= arr
    boolmask = 5 <= arr
    for i in arr.indices:
      if arr[i] >= 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr <= arr
    var allfives = emptyLike(arr)
    allfives.fill(5)

    boolmask = arr <= allfives
    for i in arr.indices:
      if arr[i] <= 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test "> works":

    # arr > scalar
    var boolmask = arr > 5
    for i in arr.indices:
      if arr[i] > 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar > arr
    boolmask = 5 > arr
    for i in arr.indices:
      if arr[i] < 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr == arr
    var allfives = emptyLike(arr)
    allfives.fill(5)

    boolmask = arr > allfives
    for i in arr.indices:
      if arr[i] > 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test ">= works":

    # arr >= scalar
    var boolmask = arr >= 5
    for i in arr.indices:
      if arr[i] >= 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false
    
    # scalar >= arr
    boolmask = 5 >= arr
    for i in arr.indices:
      if arr[i] <= 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

    # arr >= arr
    var allfives = emptyLike(arr)
    allfives.fill(5)

    boolmask = arr >= allfives
    for i in arr.indices:
      if arr[i] >= 5:
        check boolmask[i] == true
      else:
        check boolmask[i] == false

  test "`not` works":
    var notmask = not arr
    for ix in notmask.indices:
      check notmask[ix] == not arr[ix]

  test "`+=` works":
    var temp = arr.deepCopy
    temp += 1 
    for ix in temp.indices:
      check temp[ix] == arr[ix] + 1

  test "`-=` works":
    var temp = arr.deepCopy
    temp -= 1 
    for ix in temp.indices:
      check temp[ix] == arr[ix] - 1

  test "`*=` works":
    var temp = arr.deepCopy
    temp *= 2 
    for ix in temp.indices:
      check temp[ix] == arr[ix] * 2 

  test "`/=` works":
    var temp = arr.toFloat
    temp /= 2 
    for ix in temp.indices:
      check temp[ix] == arr[ix] / 2 

  test "string \"add\" works":

    var strarr = empty[string]([3])
    strarr[0] = "zed"
    strarr[1] = "is"
    strarr[2] = "dead"
    strarr.add("haha")
    check strarr[0] == "zedhaha"
    check strarr[1] == "ishaha"
    check strarr[2] == "deadhaha"

    var after = empty[string]([3])
    after[0] = "dez"
    after[1] = "si"
    after[2] = "daed"
    strarr.add(after)
    check strarr[0] == "zedhahadez"
    check strarr[1] == "ishahasi"
    check strarr[2] == "deadhahadaed"

  test "string \"&=\" works":

    var strarr = empty[string]([3])
    strarr[0] = "zed"
    strarr[1] = "is"
    strarr[2] = "dead"
    strarr &= "haha"
    check strarr[0] == "zedhaha"
    check strarr[1] == "ishaha"
    check strarr[2] == "deadhaha"

    var after = empty[string]([3])
    after[0] = "dez"
    after[1] = "si"
    after[2] = "daed"
    strarr &= after
    check strarr[0] == "zedhahadez"
    check strarr[1] == "ishahasi"
    check strarr[2] == "deadhahadaed"

  test "string \"&\" works":

    var strarr = empty[string]([3])
    strarr[0] = "zed"
    strarr[1] = "is"
    strarr[2] = "dead"
    strarr = strarr & "haha"
    check strarr[0] == "zedhaha"
    check strarr[1] == "ishaha"
    check strarr[2] == "deadhaha"

    var after = empty[string]([3])
    after[0] = "dez"
    after[1] = "si"
    after[2] = "daed"
    strarr = strarr & after
    check strarr[0] == "zedhahadez"
    check strarr[1] == "ishahasi"
    check strarr[2] == "deadhahadaed"

  test "^ works":

    var temp = arr^2
    for ix in temp.indices:
      check temp[ix] == arr[ix]^2

    temp = 2^arr
    for ix in temp.indices:
      check temp[ix] == 2^arr[ix]

    var evenodd = arr mod 2
    temp = arr^evenodd
    for ix in temp.indices:
      if arr[ix] mod 2 == 0:
        check temp[ix] == 1
      else:
        check temp[ix] == arr[ix]

  test "+ works":

    var temp = arr+2
    for ix in temp.indices:
      check temp[ix] == arr[ix]+2

    temp = 2+arr
    for ix in temp.indices:
      check temp[ix] == 2+arr[ix]

    var evenodd = arr mod 2
    temp = arr+evenodd
    for ix in temp.indices:
      if arr[ix] mod 2 == 0:
        check temp[ix] == arr[ix] 
      else:
        check temp[ix] == arr[ix] + 1

  test "`binom` works":

    var temp = binom(arr, 2)
    for ix in temp.indices:
      check temp[ix] == binom(arr[ix], 2)

    temp = binom(35, arr)
    for ix in temp.indices:
      check temp[ix] == binom(35, arr[ix])

    var evenodd = arr mod 2
    temp = binom(arr, evenodd)
    for ix in temp.indices:
      if arr[ix] mod 2 == 0:
        check temp[ix] == binom(arr[ix], 0)
      else:
        check temp[ix] == binom(arr[ix], 1)


  # FIXME check other binary operations


  test "\"sqrt\" works":
    var temp = toFloat(arr)
    temp = sqrt(temp) 
    for ix in temp.indices:
      check temp[ix] == sqrt(float(arr[ix]))


  # FIXME check other unary operations
  
  var boolmask = arr > 5
  var maskedarr = arr[boolmask] + 100
  echo maskedarr
  echo arr

  arr[boolmask] = arr[boolmask] + 100 
  echo arr[boolmask]
