use "ast.sml";

exception AddException of string * string;
exception ArithmeticException of binaryOperator * string * string;
exception AssignmentTargetException;
exception BooleanFirstException of binaryOperator * string;
exception BooleanSecondException of binaryOperator * string;
exception CallTooManyArgumentsException;
exception CallTooFewArgumentsException;
exception ClassRedeclarationException of string;
exception ConditionalException of string;
exception FieldNotFoundException of string;
exception FieldGetNonObjectException of string * string;
exception FieldSetNonObjectException of string * string;
exception IfGuardException of string;
exception NewException of string;
exception NonFunctionException of string;
exception RelationalException of binaryOperator * string * string;
exception ReturnOutsideFunctionException;
exception UnaryMinusException of string;
exception UnaryNotException of string;
exception UndeclaredVariableAssignmentException of string;
exception UndeclaredVariableException of string;
exception UnknownSuperException of string * string;
exception VariableRedeclarationException of string;
exception WhileGuardException of string;
exception ZeroDivideException;

exception ReturnException of value;