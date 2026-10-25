#!/usr/bin/env bash
# Regenerate theories/Core/JdkTables.v from the running JDK (21) by reflection.
set -euo pipefail
cd "$(dirname "$0")/.."
JAVA_HOME=${JAVA_HOME:-/usr/lib/jvm/java-1.21.0-openjdk-amd64}
w=$(mktemp -d)
"$JAVA_HOME/bin/javac" -d "$w" tools/GenJdkTables.java
L=java/lang
classes="$L/Object $L/Enum $L/Record $L/Throwable $L/Exception $L/RuntimeException $L/Error $L/Number
 $L/ArithmeticException $L/NullPointerException $L/IndexOutOfBoundsException $L/ArrayIndexOutOfBoundsException
 $L/NegativeArraySizeException $L/ClassCastException $L/ArrayStoreException $L/IllegalMonitorStateException
 $L/IllegalArgumentException $L/IllegalStateException $L/UnsupportedOperationException
 $L/StringIndexOutOfBoundsException $L/NumberFormatException java/util/NoSuchElementException
 java/util/ConcurrentModificationException $L/CloneNotSupportedException $L/LinkageError
 $L/ExceptionInInitializerError $L/NoClassDefFoundError $L/VirtualMachineError $L/StackOverflowError
 $L/OutOfMemoryError $L/AssertionError $L/IncompatibleClassChangeError $L/AbstractMethodError
 $L/NoSuchFieldError $L/NoSuchMethodError $L/IllegalAccessError $L/MatchException
 java/io/Serializable $L/Cloneable $L/Comparable $L/CharSequence $L/Appendable $L/constant/Constable
 $L/constant/ConstantDesc $L/Runnable $L/AutoCloseable $L/Iterable java/util/Comparator
 $(for f in BiConsumer BiFunction BiPredicate BinaryOperator BooleanSupplier Consumer DoubleBinaryOperator \
   DoubleConsumer DoubleFunction DoublePredicate DoubleSupplier DoubleToIntFunction DoubleToLongFunction \
   DoubleUnaryOperator Function IntBinaryOperator IntConsumer IntFunction IntPredicate IntSupplier \
   IntToDoubleFunction IntToLongFunction IntUnaryOperator LongBinaryOperator LongConsumer LongFunction \
   LongPredicate LongSupplier LongToDoubleFunction LongToIntFunction LongUnaryOperator ObjDoubleConsumer \
   ObjIntConsumer ObjLongConsumer Predicate Supplier ToDoubleBiFunction ToDoubleFunction ToIntBiFunction \
   ToIntFunction ToLongBiFunction ToLongFunction UnaryOperator; do echo java/util/function/$f; done)"
"$JAVA_HOME/bin/java" -cp "$w" GenJdkTables $classes > theories/Core/JdkTables.v
rm -rf "$w"
echo "wrote theories/Core/JdkTables.v"
