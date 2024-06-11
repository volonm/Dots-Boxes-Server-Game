package game.control;

import game.model.*;

import java.util.InputMismatchException;
import java.util.Scanner;

/**
 * Represents a human player in a game. It extends the AbstractPlayer class
 * and allows the user to make moves by entering input through the console.
 */
public class HumanPlayer extends AbstractPlayer{


    /**
     * The Scanner object to read the user input of the Human player.
     */
    private final Scanner scanner;

    /**
     * Constructor to create the HumanPlayer object which extends the Abstract Player.
     *
     * @param name name of the HumanPlayer
     * @param m mark of the HumanPlayer.
     */
    //@ requires name != null && m != null;
    //@ ensures super.getName() == name && super.getMark() == m;
    public HumanPlayer(String name, Mark m) {
        super(name,m);
        this.scanner = new Scanner(System.in);
    }

    /**
     * Determines the next move for the HumanPlayer by prompting the user for input.
     * Continues prompting until a valid move is entered.
     *
     * @param game the Game instance in which the HumanPlayer is participating
     * @return a Move representing the user's chosen move
     */
    @Override
    public Move determineMove(Game game) {
        int index = -1;
        Move move = null;
        boolean isNotValid = true;
        while (isNotValid) {
            while (index < 0 || index > Board.DIM) {
                try {
                    System.out.println("Enter the move");
                    index = scanner.nextInt();
                } catch (InputMismatchException e) {
                    scanner.nextLine();
                    System.out.println("Invalid input for the index !!!");
                }
            }
            move = new MoveGame(index, super.getMark());
            if(game.isValidMove(move)){
                isNotValid = false;
            }
        }
        return move;
    }
}
