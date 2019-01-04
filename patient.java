package insulin;

public class Patient {
    private int glucose;
    private int insulindose;
   

    /*@ public ghost \seq patientViewInsulinPump;
      @ public invariant patientViewInsulinPump == \seq(this, glucose);
      @*/

    public int getGlucose() {
        return glucose;
    }

    /*@ normal_behavior
      @ determines patientViewInsulinPump \by  \itself
      @ \declassifies insulindose;
      @ assignable glucose, patientViewInsulinPump;
      @*/
    public void foodIntake(int insulindose) {
        this.insulindose = (glucose - 144)/50;
        /*@ set patientViewInsulinPump =
                    \seq_concat(\seq_singleton(this),
                    \seq_concat(\seq_singleton(glucose),
                        \seq_singleton(insulindose)));
        */;
    }
}
