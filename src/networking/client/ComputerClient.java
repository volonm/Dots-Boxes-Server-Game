package networking.client;

import game.control.HumanPlayer;
import game.control.ai.ComputerPlayer;
import game.control.ai.NaiveStrategy;
import game.control.ai.SmartStrategy;
import game.model.GameImpl;
import game.model.Mark;
import game.model.Move;
import game.model.MoveGame;
import networking.protocol.Protocol;

import java.io.IOException;

public class ComputerClient extends Client{

    private ComputerPlayer computerPlayer;
    private boolean smart;


    /**
     * Constructor for the game client.
     *
     * @param address the address of the server
     * @param port    the port to connect to
     * @throws IOException if an I/O error occurs while creating the ClientConnection
     */
    public ComputerClient(String address, int port) throws IOException {
        super(address, port);
    }

    /**
     * Sends a username to the server.
     *
     * @param username the username to be sent
     */
    @Override
    public void sendUsername(String username) {
        String[] split = username.split(Protocol.SEPARATOR);
            smart = split[1].equalsIgnoreCase("Smart");
        this.username = split[0];
        clientConnection.sendUsername(split[0]);
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
            case "HINT":
                provideHint();
                break;
            default:
                listener.message(Protocol.ERROR + Protocol.SEPARATOR + "Not a command");
                break;
        }
    }

    private void handleQueueCommand() {
        clientConnection.sendQueue();
        listener.message("Joined the queue");
        if (smart){
            listener.message("Playing as smart AI");
        } else {
            listener.message("Playing as naive AI");
        }
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
                handleNewComputerGame(split);
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
    private void handleNewComputerGame(String[] split) {
        active = true;
        listener.message("Game started!");
        listener.message("Player 1: " + split[1]);
        listener.message("Player 2: " + split[2]);
            initializeComputerGame(split[1], split[2]);
    }

    /**
     * Starts a game on the client side if the client plays as a computer
     * @param player1 the first player
     * @param player2 the second player
     */
    private void initializeComputerGame(String player1, String player2) {
        if (player1.equalsIgnoreCase(username)) {
            if (smart) {
                computerPlayer = new ComputerPlayer(new SmartStrategy(), Mark.BLUE);
            } else {
                computerPlayer = new ComputerPlayer(new NaiveStrategy(), Mark.BLUE);
            }
            game = new GameImpl(computerPlayer, new HumanPlayer(player2, Mark.RED));
            turn = true;
            opponent = player2;
            mark = Mark.BLUE;
        } else {
            if (smart) {
                computerPlayer = new ComputerPlayer(new SmartStrategy(), Mark.RED);
            } else {
                computerPlayer = new ComputerPlayer(new NaiveStrategy(), Mark.RED);

            }
            game = new GameImpl(new HumanPlayer(player1, Mark.BLUE), computerPlayer);
            opponent = player1;
            mark = Mark.RED;
        }

        listener.message(game.getBoard().toString());
        listener.message("Turn: " + (turn ? username : opponent));
        if (turn){
            int move = computerPlayer.determineMove(game).getIndex();
            clientConnection.sendMove(String.valueOf(move));
        }
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
        //play move immediately if playing as AI
        if (turn && !game.isGameOver()) {
            int index = computerPlayer.determineMove(game).getIndex();
            clientConnection.sendMove(String.valueOf(index));
        }
    }
}
