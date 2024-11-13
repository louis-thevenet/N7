import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * 
 */
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface UnTest {
  static class None extends Throwable {
  }

  boolean enabled() default true;

  Class<? extends Throwable> expected() default None.class;
}
