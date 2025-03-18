class OperationNonConfirmeeException extends RuntimeException
{
      // Parameterless Constructor
      public OperationNonConfirmeeException() {}

      // Constructor that accepts a message
      public OperationNonConfirmeeException(String message)
      {
         super(message);
      }
 }