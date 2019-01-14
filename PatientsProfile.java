

//Given("^User is trying to see patient's profile$")

public class PatientsProfile {
    private User[] Users;
    private int patientsProfile;

    /*@ normal_behavior
      @ determines u, u.profile,
      @            hasPrivilege(u),
      @            (hasPrivilege(u) ? patientsProfile : 0)
      @        \by \itself;
      @*/

//When("^User has access privilege to patient's profile$")
    
    public void getPatientsProfile(User u) {
        if (hasPrivilege(u)) {
            u.setProfile(patientsProfile);
        }
    }

    /*@ normal_behavior
      @ ensures \result ==
      @         (\exists int i; 0 <= i && i < Users.length;
      @                                             Users[i] == u);
      @*/
    private /*@ pure */ boolean hasPrivilege(User u) {
        /*@ loop_invariant 0 <= i && i <= Users.length;
          @ loop_invariant
          @     (\forall int j; 0 <= j && j < i; Users[j] != u);
          @ assignable \nothing;
          @ decreases Users.length - i;
          @*/
        for (int i = 0; i < Users.length; i++) {
            if (Users[i] == u) {
                return true;
            }
        }
        return false;
    }
//Then("^User can read patient's profile$")

    public class User {
        private /*@ spec_public */ int profile;

        void setProfile(int profile) {
            this.profile = profile;
        }
    }
}


//When("^user name and password are in the user index$")


class UserPasswordFile {

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
    
 //Then("^user has privilege to the profile$")

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
