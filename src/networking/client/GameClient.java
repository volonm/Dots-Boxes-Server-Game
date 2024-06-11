package networking.client;

import game.control.HumanPlayer;
import game.model.GameImpl;
import game.model.Mark;

import game.model.Move;
import game.model.MoveGame;
import networking.protocol.Protocol;

import java.io.IOException;

/**
 * The client for Dots & Boxes
 * handles all user input and server response
 */
public class GameClient extends Client{

    /**
     * Constructor for the game client.
     *
     * @param address the address of the server
     * @param port    the port to connect to
     * @throws IOException if an I/O error occurs while creating the ClientConnection
     */
    public GameClient(String address, int port) throws IOException {
        super(address, port);
        clientConnection = new ClientConnection(address, port, this);
    }

    /**
     * Sends the specified command to the server
     *
     * @param command the command to be sent
     */
    @Override
    public void sendCommand(String command) {
        String[] split = command.split(Protocol.SEPARATOR);
        String commandType = split[0].toUpperCase();

        switch (commandType) {
            case Protocol.LIST:
                handleListCommand();
                break;
            case Protocol.QUEUE:
                handleQueueCommand();
                break;
            case Protocol.MOVE:
                handleMoveCommand(split);
                break;
            case "HINT":
                provideHint();
                break;
            default:
                listener.message(Protocol.ERROR + Protocol.SEPARATOR + "Not a command");
                break;
        }
    }

    /**
     * Sends queue command to the server.
     */
    private void handleQueueCommand() {
        clientConnection.sendQueue();
        listener.message("Joined the queue");
    }

    /**
     * Handles a message received from the server.
     *
     * @param message the chat message received from the server
     */
    @Override
    public void receiveMessage(String message) {
        String[] split = message.split(Protocol.SEPARATOR);
        String command = split[0];

        switch (command) {
            case Protocol.LOGIN:
                handleLogin(split);
                break;

            case Protocol.LIST:
                handleList(split);
                break;

            case Protocol.NEWGAME:
                handleNewHumanGame(split);
                break;

            case Protocol.ALREADYLOGGEDIN:
                handleAlreadyLoggedIn(split);
                break;

            case Protocol.MOVE:
                handleMove(split);
                break;

            case Protocol.GAMEOVER:
                handleGameOver(message);
                break;

            default:
                // Do nothing, server sent an invalid message
                break;
        }
    }

    /**
     * Handles the NEW GAME command from the server
     * @param split the full server message
     */
    private void handleNewHumanGame(String[] split) {
        active = true;
        listener.message("Game started!");
        listener.message("Player 1: " + split[1]);
        listener.message("Player 2: " + split[2]);
        initializeHumanGame(split[1], split[2]);
    }

    /**
     * Starts a game on the client side if the client plays as a human
     * @param player1 the first player
     * @param player2 the second player
     */
    private void initializeHumanGame(String player1, String player2) {
        game = new GameImpl(new HumanPlayer(player1, Mark.BLUE), new HumanPlayer(player2, Mark.RED));
        if (player1.equalsIgnoreCase(username)) {
            turn = true;
            opponent = player2;
            mark = Mark.BLUE;
        } else {
            opponent = player1;
            mark = Mark.RED;
        }

        listener.message(game.getBoard().toString());
        listener.message("Turn: " + (turn ? username : opponent));
    }

    /**
     * Handles the move command from the server
     * @param split the command from the server
     */
    void handleMove(String[] split) {
        Move move = new MoveGame(Integer.parseInt(split[1]), turn ? mark : mark.other());
        game.doMove(move);

        listener.message(game.getBoard().toString());
        listener.message("Move played: " + split[1]);

        if (game.completesSquare(move.getIndex())) { // keep turn of square was completed
            listener.message("Turn: " + (turn ? username : opponent));
        } else {
            turn = !turn;
            listener.message("Turn: " + (turn ? username : opponent));
        }
        listener.message("\n");
    }
}
