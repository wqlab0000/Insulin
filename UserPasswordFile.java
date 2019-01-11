//When("^user name and password are in the user index$")


class SUserPasswordFile {

    /*@ public final model \locset footprint; 
      @ represents footprint =
      @     \locset(names, passwords), names[*], passwords[*];
      @*/

    /*@ model int userIndex;
      @ represents userIndex \such_that
      @     0 <= userIndex && userIndex < names.length;
      @ accessible userIndex : \locset(names);
      @*/

    /*@ invariant   names.length == passwords.length;
      @*/
    
    private int[] names;
    private int[] passwords;


    public SecurePasswordFile(int[] names, int[] passwords) {
        this.names = names;
        this.passwords = passwords;
    }


    /**
     * Returns whether password is correct.
     */
    
 //Then("^user has privilege to the profile if name and password are in the user index$")

    public boolean check(int user, int password) {
        /*@ loop_invariant
          @     0 <= i
          @  && i <= names.length
          @  && (\forall int j; 0 <= j && j < i;
          @         !(names[j] == user && passwords[j] == password));
          @ assignable \nothing;
          @ decreases names.length - i;
          @*/
        for (int i = 0; i < names.length; i++) {
            if (names[i] == user &&
                passwords[i] == password) {
                return true;
            }
        }
        return false;
    }
}
