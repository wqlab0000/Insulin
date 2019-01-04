//package insulin;

//import org.junit.runner.RunWith;

//RunWith(Insulin.class)
//Cucumber.Options(
//format = {"pretty", "json:target/"},
//features = {"src/insulin/"})


//Given("^insulin pump is turned on$")
public class Insulin{
    private /*@ spec_public @*/ String insulinpump;

    /*@ public invariant glucose >= 70;
      @
      @*/

//Given ("^insulin pump delivers basal rate of insulin")

    private /*@ spec_public @*/ int glucose;

    /*@ public invariant glucose <= 250 ==> !bolus &&
      @                  glucose > 250 ==> bolus;
      @*/
    private /*@ spec_public @*/ boolean bolus;

    /*@ requires g >= 0;
      @ ensures glucose == \old(glucose) + g;
      @ assignable glucose, bolus;
      @*/
    
    

//When("^patient's blood glucose level is not less than (\\d+)$")

    public void readGlucose(int g) {
        updateGlucose(g);
        if (glucose > 250) {
            changeToBolus();
        }
    }

    /*@ requires g >= 0;
      @ ensures glucose == \old(glucose) + g;
      @ assignable glucose;
      @*/
    private void updateGlucose(int g) {
    	glucose += g;
    }

    /*@ requires glucose > 250;
      @ ensures bolus;
      @ assignable bolus;
      @*/
    

//Then("^insulin pump status change to deliver bolus rate of insulin$")

    private void changeToBolus() {
        bolus = true;
    }

    /*@ ensures this.insulinpump == insulinpump;
      @ assignable this.insulinpump;
      @*/
    public void setInsulinpump(String insulinpump) {
        this.insulinpump = insulinpump;
    }

    /*@ ensures \result == insulinpump;
      @*/
    public /*@ pure @*/ String getInsulinpump() {
        return insulinpump;
    }
}
