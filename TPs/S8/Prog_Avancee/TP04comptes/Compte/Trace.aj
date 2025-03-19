public aspect Trace {
    pointcut publicMethods(): 
        call(public * (CompteSimple||CompteCourant).*(..))
		|| call(public (CompteSimple||CompteCourant).new(..));        

    before():publicMethods() {
        String trace_msg = thisJoinPoint.getSignature().getName() + "(";
        for (Object arg : thisJoinPoint.getArgs()) {
            trace_msg += (arg.toString()) + ", ";
        }
        if (thisJoinPoint.getArgs().length > 0) {
            trace_msg = trace_msg.substring(0, trace_msg.length()-2);
        }
        trace_msg += ")";
        System.out.println(trace_msg);
    }
}