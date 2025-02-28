import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.util.List;

public class Protection implements InvocationHandler {
  private Object obj;

  private List<String> methodsToForbid;

  public Protection(Object obj, List<String> methodsToForbid) {
    this.obj = obj;
    this.methodsToForbid = methodsToForbid;
  }

  @Override
  public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
    if (this.methodsToForbid.contains(
        method.getName())) {
      throw new UnsupportedOperationException();
    }
    return method.invoke(this.obj, args);

  }

}
