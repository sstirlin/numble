import strutils
import macros
import sequtils
import unittest
import typetraits


{.experimental.}  # for automatic dereferencing


type

  SlicedArray*[T] = object of RootObj

    shape*: seq[int]
    ndim*: int
    size*: int
    strides*: seq[int]
    offset*: int
    data*: ptr seq[T]  # usually points to dataPrivate
    dataPrivate: seq[T]


proc initNilSlicedArray[T](shape: openarray[int]): SlicedArray[T] =

  result.data = nil
  result.shape = @shape  # copies deeply
  result.ndim = len(shape)
  result.size = shape.foldl(a*b)
  for i in result.shape:
    if i < 1:
      raise newException(RangeError, "SlicedArray shape must be list of integers > 0")

  result.strides = newSeq[int](result.ndim)
  result.strides[result.ndim-1] = 1
  for i in countdown(result.ndim-1, 1):
    result.strides[i-1] = result.strides[i]*shape[i]

  result.offset = 0


proc initSlicedArray*[T](shape: openarray[int]): SlicedArray[T] =

    result = initNilSlicedArray[T](shape)
    result.dataPrivate = newSeq[T](result.size)
    shallow(result.dataPrivate)  # only allow shallow copies
    result.data = addr(result.dataPrivate)


proc initSlicedArrayOnSeq*[T](shape: openarray[int], data: ptr seq[T]): SlicedArray[T] =

  result = initNilSlicedArray[T](shape)
  if result.size > len(data):
    raise newException(RangeError, "SlicedArray shape is larger than provided buffer")

  result.data = data


proc `[]`*[T](arr: SlicedArray[T], ix: varargs[int]): var T =

  var args = @ix  # varargs are not mutable

  when compileOption("boundChecks"):
    if len(args) != arr.ndim:
      raise newException(IndexError, "SlicedArray index must match shape")

  var flatix = arr.offset
  for i in 0..(len(args)-1):
    when compileOption("boundChecks"):
      if args[i] >= arr.shape[i] or args[i] < -arr.shape[i]:
        raise newException(IndexError, "SlicedArray index is out of bounds")
    if args[i] < 0:
      args[i] += arr.shape[i]
    flatix += args[i] * arr.strides[i]

  result = arr.data[flatix]


proc `[]=`*[T](arr: SlicedArray[T], ix: varargs[int], rhs: T) =

  when compileOption("boundChecks"):
    if len(ix) != arr.ndim:
      raise newException(IndexError, "SlicedArray index must match shape")

  var flatix = arr.offset
  for i, v in ix:
    when compileOption("boundChecks"):
      if v >= arr.shape[i] or v < -arr.shape[i]:
        raise newException(IndexError, "SlicedArray index is out of bounds")
    var temp = v
    if v < 0:
      temp += arr.shape[i]
    flatix += temp * arr.strides[i]

  arr.data[flatix] = rhs


type

  SteppedSlice* = object of RootObj
    a*, b*: int 
    step*: int
    incEnd*: bool


proc initSteppedSlice*(a, b, step: int, incEnd: bool): SteppedSlice =

    result.a = a
    result.b = b
    result.step = step
    result.incEnd = incEnd


const _ = high(int)
    

macro `[]`[T](arr: SlicedArray[T], e: string): expr =

    var args = split(e.strVal, ",")
    var code = $arr & "["

    for i in 0.. <len(args):
        if strip(args[i]) == "...":
            code.add("fill")
        else:
            var ixs = split(strip(args[i]), ":")
            if len(ixs) == 0 or len(ixs) > 3:
                error("SlicedArray slice index is invalid")
            elif len(ixs) == 1:
                code.add(ixs[0])
            elif len(ixs) > 1:
                # convert from pythonic [,) to nimlike [,] intervals
                if strip(ixs[0]) == "":
                    ixs[0] = $_
                if strip(ixs[1]) == "":
                    ixs[1] = $_
                if len(ixs) == 3: # see if we should step other than default
                    if strip(ixs[2]) == "":
                        ixs[2] = "1"
                else:
                    ixs.add("1")
                code.add("int(")
                code.add(ixs[0])
                code.add(")")
                code.add("...")
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


proc `..`*(a: int, b: int): SteppedSlice =

    result.a = a
    result.b = b
    result.step = 1
    result.incEnd = true


proc `..-`*(a: int, b: int): SteppedSlice =

    result.a = a
    result.b = -b
    result.step = 1
    result.incEnd = true


proc `..+`*(a: int, b: int): SteppedSlice =

    result.a = a
    result.b = b
    result.step = 1
    result.incEnd = true


proc `..`*(a: int, s: SteppedSlice): SteppedSlice =

    result.a = a
    result.b = s.b
    result.step = s.step
    result.incEnd = true


proc `..-`*(a: int, s: SteppedSlice): SteppedSlice =

    result.a = a
    result.b = -s.b
    result.step = s.step
    result.incEnd = true


proc `..+`*(a: int, s: SteppedSlice): SteppedSlice =

    result.a = a
    result.b = s.b
    result.step = s.step
    result.incEnd = true


proc `...`*(a: int, b: int): SteppedSlice =

    result.a = a
    result.b = b
    result.step = 1
    result.incEnd = false


proc `...-`*(a: int, b: int): SteppedSlice =

    result.a = a
    result.b = -b
    result.step = 1
    result.incEnd = false


proc `...+`*(a: int, b: int): SteppedSlice =

    result.a = a
    result.b = b
    result.step = 1
    result.incEnd = false


proc `...`*(a: int, s: SteppedSlice): SteppedSlice =

    result.a = a
    result.b = s.b
    result.step = s.step
    result.incEnd = false


proc `...-`*(a: int, s: SteppedSlice): SteppedSlice =

    result.a = a
    result.b = -s.b
    result.step = s.step
    result.incEnd = false


proc `...+`*(a: int, s: SteppedSlice): SteppedSlice =

    result.a = a
    result.b = s.b
    result.step = s.step
    result.incEnd = false


proc `|`*(b: int, step: int): SteppedSlice =

    result.a = 0
    result.b = b
    result.step = step
    result.incEnd = true


proc `|-`*(b: int, step: int): SteppedSlice =

    result.a = 0
    result.b = b
    result.step = -step
    result.incEnd = true


proc `|+`*(b: int, step: int): SteppedSlice =

    result.a = 0
    result.b = b
    result.step = step
    result.incEnd = true


proc `|`*(s: SteppedSlice, step: int): SteppedSlice =

    result.a = s.a
    result.b = s.b
    result.step = step
    result.incEnd = s.incEnd


proc `|-`*(s: SteppedSlice, step: int): SteppedSlice =

    result.a = s.a
    result.b = s.b
    result.step = -step
    result.incEnd = s.incEnd


proc `|+`*(s: SteppedSlice, step: int): SteppedSlice =

    result.a = s.a
    result.b = s.b
    result.step = step
    result.incEnd = s.incEnd


proc `..|`*(step: int): SteppedSlice =

    result.a = _
    result.b = _
    result.step = step
    result.incEnd = true


proc `..|-`*(step: int): SteppedSlice =

    result.a = _
    result.b = _
    result.step = -step
    result.incEnd = true


proc `..|+`*(step: int): SteppedSlice =

    result.a = _
    result.b = _
    result.step = step
    result.incEnd = true


let fill = initSteppedSlice(0,0,0,true)


proc `[]`*[T](arr: SlicedArray[T], ix: varargs[SteppedSlice]): SlicedArray[T] =

    var args = newSeq[SteppedSlice](0)
    
    # If 'fill' specified in front or back then expand it
    if ix[0] == fill:
        for i in 1..(len(ix)-1):
            if ix[i] == fill:
                raise newException(IndexError, "'fill' is only allowed either at the front or back of an SlicedArray, and never at the same time")
        for i in 1..(arr.ndim-(len(ix)-1)):
            args.add(..|1)
        for i in 1..(len(ix)-1):
            args.add(ix[i])
    elif ix[len(ix)-1] == fill:
        for i in 0..(len(ix)-2):
            if ix[i] == fill:
                raise newException(IndexError, "'fill' is only allowed either at the front or back of an SlicedArray, and never at the same time")
        for i in 0..(len(ix)-2):
            args.add(ix[i])
        for i in 1..(arr.ndim-(len(ix)-1)):
            args.add(..|1)
    else:
        for i in 0..(len(ix)-1):
            args.add(ix[i])

    if len(args) != arr.ndim:
        raise newException(IndexError, "new SlicedArray must have same shape as original")

    result = arr

    # first check that ranges make sense
    for i in 0..(len(args)-1):
        
        if args[i].step < 0:
            if args[i].b == _:
                args[i].b = 0
            else:
                if not args[i].incEnd:
                    args[i].b += 1
            if args[i].a == _:
                args[i].a = arr.shape[i]-1 
        else:
            if args[i].b == _:
                args[i].b = arr.shape[i]-1 
            else:
                if not args[i].incEnd:
                    args[i].b -= 1
            if args[i].a == _:
                args[i].a = 0

        if args[i].a >= arr.shape[i] or args[i].a < -arr.shape[i]:
                raise newException(IndexError, "SlicedArray index is out of bounds")
        if args[i].b >= arr.shape[i] or args[i].b < -arr.shape[i]:
                raise newException(IndexError, "SlicedArray index is out of bounds")
        if args[i].a < 0:
            args[i].a += arr.shape[i]
        if args[i].b < 0:
            args[i].b += arr.shape[i]
        args[i].b -= (args[i].b - args[i].a) mod args[i].step  # make array bounds evenly divisible by stepsize
        if (args[i].b - args[i].a) div args[i].step < 0:
            raise newException(IndexError, "SlicedArray must have range in same direction as step")

    # set offset
    for i, v in args:
        result.offset += v.a * result.strides[i]

    # set shape and strides    
    result.size = 1
    for i, v in args:
        result.strides[i] *= v.step
        result.shape[i] = abs((v.b - v.a) div v.step) + 1
        result.size *= result.shape[i]


iterator flat[T](arr: SlicedArray[T]): seq[int] =

  var counters = newSeq[int](arr.ndim)
  for dim in 0..<arr.ndim:
    counters[dim]=0
  for i in 0..<arr.size:
    yield counters
    for dim in countdown(arr.ndim-1,0):
      counters[dim] += 1
      if counters[dim] == arr.shape[dim]:
        counters[dim] = 0
      else:
        break


macro generateBinaryOpSlicedArrayTScalarT(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: SlicedArray[$2], s: $2): SlicedArray[$3] =

               result = initSlicedArray[$3](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2](arr[ix], s) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


macro generateBinaryOpScalarTSlicedArrayT(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](s: $2, arr: SlicedArray[$2]): SlicedArray[$3] =

               result = initSlicedArray[$3](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2](s, arr[ix]) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


macro generateBinaryOpSlicedArrayTSlicedArrayT(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: SlicedArray[$2], s: SlicedArray[$2]): SlicedArray[$3] =

               if arr.shape != s.shape:
                 raise newException(RangeError, "SlicedArrays must have same shape")

               result = initSlicedArray[$3](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2](arr[ix], s[ix]) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


macro generateBinaryOpSlicedArrayTScalarS(op, T, S, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2, $3](arr: SlicedArray[$2], s: $3): SlicedArray[$4] =

               result = initSlicedArray[$4](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2, $3](arr[ix], s) 
             """ % [opstr, $T, $S, $Tout]
  result = parseStmt(body)


macro generateBinaryOpScalarSSlicedArrayT(op, S, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2, $3](s: $2, arr: SlicedArray[$3]): SlicedArray[$4] =

               result = initSlicedArray[$4](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2, $3](s, arr[ix]) 
             """ % [opstr, $S, $T, $Tout]
  result = parseStmt(body)


macro generateBinaryOpSlicedArrayTSlicedArrayS(op, T, S, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2, $3](arr: SlicedArray[$2], s: SlicedArray[$3]): SlicedArray[$4] =

               if arr.shape != s.shape:
                 raise newException(RangeError, "SlicedArrays must have same shape")

               result = initSlicedArray[$4](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2, $3](arr[ix], s[ix]) 
             """ % [opstr, $T, $S, $Tout]
  result = parseStmt(body)


macro generateInplaceOpSlicedArrayTScalarT(op, T: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: var SlicedArray[$2], s: $2) =

               for ix in arr.flat:
                 $1(arr[ix], s) 
             """ % [opstr, $T]
  result = parseStmt(body)


macro generateInplaceOpSlicedArrayTSlicedArrayT(op, T: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: var SlicedArray[$2], s: SlicedArray[$2]) =

               if arr.shape != s.shape:
                 raise newException(RangeError, "SlicedArrays must have same shape")

               for ix in arr.flat:
                 $1(arr[ix], s[ix]) 
             """ % [opstr, $T]
  result = parseStmt(body)


macro generateUnaryOpSlicedArrayT(op, T, Tout: expr): stmt {.immediate.} =

  var opstr = "" 
  if op.kind == nnkAccQuoted:
    opstr = "`" & $(op[0]) & "`"
  else:
    opstr = $op
  let body = """
             proc $1*[$2](arr: SlicedArray[$2]): SlicedArray[$3] =

               result = initSlicedArray[$3](arr.shape)
               for ix in arr.flat:
                 result[ix] = $1[$2](arr[ix]) 
             """ % [opstr, $T, $Tout]
  result = parseStmt(body)


generateBinaryOpSlicedArrayTScalarT(`==`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`!=`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`<`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`<=`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`>`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`>=`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`+`, T, T)
generateBinaryOpSlicedArrayTScalarT(`-`, T, T)
generateBinaryOpSlicedArrayTScalarT(`*`, T, T)
generateBinaryOpSlicedArrayTScalarT(`/`, T, T)
generateBinaryOpSlicedArrayTScalarT(`==%`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`<%`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`<=%`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`>%`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`>=%`, T, bool)
generateBinaryOpSlicedArrayTScalarT(`+%`, T, T)
generateBinaryOpSlicedArrayTScalarT(`-%`, T, T)
generateBinaryOpSlicedArrayTScalarT(`*%`, T, T)
generateBinaryOpSlicedArrayTScalarT(`/%`, T, T)
generateBinaryOpSlicedArrayTScalarT(`%%`, T, T)
generateBinaryOpSlicedArrayTScalarT(`div`, T, T)
generateBinaryOpSlicedArrayTScalarT(`mod`, T, T)
generateBinaryOpSlicedArrayTScalarT(`shr`, T, T)
generateBinaryOpSlicedArrayTScalarT(`shl`, T, T)
generateBinaryOpSlicedArrayTScalarT(`and`, T, T)
generateBinaryOpSlicedArrayTScalarT(`or`, T, T)
generateBinaryOpSlicedArrayTScalarT(`xor`, T, T)
generateBinaryOpSlicedArrayTScalarT(cmp, T, T)
generateBinaryOpSlicedArrayTScalarT(`&`, string, string)

generateBinaryOpScalarTSlicedArrayT(`==`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`!=`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`<`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`<=`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`>`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`>=`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`+`, T, T)
generateBinaryOpScalarTSlicedArrayT(`-`, T, T)
generateBinaryOpScalarTSlicedArrayT(`*`, T, T)
generateBinaryOpScalarTSlicedArrayT(`/`, T, T)
generateBinaryOpScalarTSlicedArrayT(`==%`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`<%`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`<=%`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`>%`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`>=%`, T, bool)
generateBinaryOpScalarTSlicedArrayT(`+%`, T, T)
generateBinaryOpScalarTSlicedArrayT(`-%`, T, T)
generateBinaryOpScalarTSlicedArrayT(`*%`, T, T)
generateBinaryOpScalarTSlicedArrayT(`/%`, T, T)
generateBinaryOpScalarTSlicedArrayT(`%%`, T, T)
generateBinaryOpScalarTSlicedArrayT(`div`, T, T)
generateBinaryOpScalarTSlicedArrayT(`mod`, T, T)
generateBinaryOpScalarTSlicedArrayT(`shr`, T, T)
generateBinaryOpScalarTSlicedArrayT(`shl`, T, T)
generateBinaryOpScalarTSlicedArrayT(`and`, T, T)
generateBinaryOpScalarTSlicedArrayT(`or`, T, T)
generateBinaryOpScalarTSlicedArrayT(`xor`, T, T)
generateBinaryOpScalarTSlicedArrayT(cmp, T, T)
generateBinaryOpScalarTSlicedArrayT(`&`, string, string)

generateBinaryOpSlicedArrayTScalarS(`is`, T, S, bool)
generateBinaryOpSlicedArrayTScalarS(`of`, T, S, bool)

generateBinaryOpScalarSSlicedArrayT(`is`, S, T, bool)
generateBinaryOpScalarSSlicedArrayT(`of`, S, T, bool)

generateInplaceOpSlicedArrayTScalarT(add, string)
generateInplaceOpSlicedArrayTScalarT(`+=`, T)
generateInplaceOpSlicedArrayTScalarT(`-=`, T)
generateInplaceOpSlicedArrayTScalarT(`*=`, T)
generateInplaceOpSlicedArrayTScalarT(`/=`, T)
generateInplaceOpSlicedArrayTScalarT(`&=`, string)

generateInplaceOpSlicedArrayTSlicedArrayT(add, string)
generateInplaceOpSlicedArrayTSlicedArrayT(`+=`, T)
generateInplaceOpSlicedArrayTSlicedArrayT(`-=`, T)
generateInplaceOpSlicedArrayTSlicedArrayT(`*=`, T)
generateInplaceOpSlicedArrayTSlicedArrayT(`/=`, T)
generateInplaceOpSlicedArrayTSlicedArrayT(`&=`, string)

generateUnaryOpSlicedArrayT(`not`, T, T)


when isMainModule:


  var raw = newSeq[int](36)
  for i in 0..35:
      raw[i] = i

  test "Size bigger than than underlying raw buffer throws RangeError":
    expect RangeError:
      discard initSlicedArrayOnSeq([3,4,4], addr(raw))

  test "Nonsensical shape throws RangeError":
    expect RangeError:
      discard initSlicedArrayOnSeq([-3,4,3], addr(raw))
    expect RangeError:
      discard initSlicedArrayOnSeq([3,-4,3], addr(raw))
    expect RangeError:
      discard initSlicedArrayOnSeq([3,4,-3], addr(raw))
    expect RangeError:
      discard initSlicedArrayOnSeq([3,-4,-3], addr(raw))
    expect RangeError:
      discard initSlicedArrayOnSeq([-3,-4,-3], addr(raw))


  var arr = initSlicedArrayOnSeq([3,4,3], addr(raw))

  test "Shape, size, ndim, strides, offset, data, are correct":
    check arr.shape == @[3,4,3]
    check arr.size == 36
    check arr.ndim == 3
    check arr.strides == @[12,3,1]
    check arr.offset == 0
    check arr.data == addr(raw)
  
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

#  echo (arr < 5).data
#  for i in arr.flat:
#    echo i
  var boolmask = arr == 5
  echo boolmask.data
  boolmask = arr <= 5
  echo boolmask.data
  boolmask = arr < 5
  echo boolmask.data
  boolmask = arr >= 5
  echo boolmask.data
  boolmask = arr > 5
  echo boolmask.data

  boolmask = 5 == arr
  echo boolmask.data
  boolmask = 5 <= arr
  echo boolmask.data
  boolmask = 5 < arr
  echo boolmask.data
  boolmask = 5 >= arr
  echo boolmask.data
  boolmask = 5 > arr
  echo boolmask.data

  var intmask = not arr
  echo intmask.data

  arr += 1
  echo arr
  arr -= 1
  echo arr


  var arr1 = initSlicedArray[string]([3])
  arr1[0] = "zed"
  arr1[1] = "blah"
  arr1[2] = "phrrt"
  arr1.add("haha")
  arr1 &= "blech"
  echo arr1.data

  var arr2 = initSlicedArray[string]([3])
  arr2[0] = "dez"
  arr2[1] = "halb"
  arr2[2] = "trrhp"
  arr1 &= arr2
  arr1.add(arr2)
  echo arr1.data
