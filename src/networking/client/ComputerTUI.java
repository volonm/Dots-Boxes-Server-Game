package networking.client;

import networking.protocol.Protocol;

import java.io.IOException;
import java.util.InputMismatchException;
import java.util.Scanner;

/**
 * The user interface for both the player and the computer
 * It allows users to connect to a server and interact with the dots & boxes environment
 */
public class ComputerTUI implements ClientListener {
    private ComputerClient computerClient;

    /**
     * Runs the TUI for the game. This method handles connecting to the server, sending
     * initial messages, displaying the menu, and processing user input.
     *
     * @throws InterruptedException if the thread is interrupted while sleeping
     */
    private void runTUI() throws InterruptedException {
        Scanner scanner = new Scanner(System.in);

        int serverPort = -1;

        connectToServer(scanner, serverPort);

        computerClient.sendHello();
        waitForConnection(scanner);

        menu();

        handleUserInput(scanner);

        scanner.close();
    }

    /**
     * Connects to the server by asking the user for a server address and port.
     * Continues until a successful connection is established.
     *
     * @param scanner    the Scanner for user input
     * @param serverPort the server port to connect to
     */
    private void connectToServer(Scanner scanner, int serverPort) {
        while (true) {
            // Ask the user for the server address and port
            System.out.print("Enter server address: ");
            String serverAddress = scanner.nextLine();

            while (serverPort < 0 || serverPort > 65535) {
                try {
                    System.out.print("Enter server port: ");
                    serverPort = scanner.nextInt();
                } catch (InputMismatchException e) {
                    System.out.println(Protocol.ERROR + Protocol.SEPARATOR + "Invalid Input");
                    scanner.nextLine();
                }
            }
            scanner.nextLine();

            try {
                computerClient = new ComputerClient(serverAddress, serverPort);
                computerClient.listener = this;
                break;
            } catch (IOException e) {
                System.out.println(Protocol.ERROR + Protocol.SEPARATOR + "Unknown host");
                serverPort = -1;
            }
        }
    }

    /**
     * Waits for the connection to be established. Prompts the user for a username and sends it to the server.
     *
     * @param scanner the Scanner for user input
     * @throws InterruptedException if the thread is interrupted while sleeping
     */
    private void waitForConnection(Scanner scanner) throws InterruptedException {
        while (!computerClient.connected) {
            Thread.sleep(100);
            System.out.print("Enter your username: ");
            String username = scanner.nextLine();
                boolean choice = false;
                while (!choice) {
                    System.out.print("Smart or Naive: ");
                    String computer = scanner.nextLine();
                    if (computer.equalsIgnoreCase("Smart")) {
                        choice = true;
                        computerClient.sendUsername(username + Protocol.SEPARATOR + "Smart");
                    } else if (computer.equalsIgnoreCase("Naive")) {
                        choice = true;
                        computerClient.sendUsername(username + Protocol.SEPARATOR + "Naive");
                    } else {
                        System.out.println(Protocol.ERROR + Protocol.SEPARATOR + "Not an option");
                    }
            }
            Thread.sleep(50);
        }
    }

    /**
     * Handles user input during the game. Allows to send commands, quit the game, or display the help menu.
     *
     * @param scanner the Scanner for user input
     */
    private void handleUserInput(Scanner scanner) {
        while (true) {
            String message = scanner.nextLine();

            if (message.equalsIgnoreCase("quit")) {
                // Terminate the connection and exit
                computerClient.close();
                break;
            } else if (message.equalsIgnoreCase("help")) {
                menu();
            } else {
                sendUserCommand(message);
            }
        }
    }

    /**
     * Sends a user command to the server. If the command is a valid move, it sends a MOVE command; otherwise, it sends
     * the command to be interpreted by the client
     *
     * @param message the user command
     */
    private void sendUserCommand(String message) {
        computerClient.sendCommand(message);
    }

    /**
     * Displays the menu of available commands.
     */
    private void menu() {
        System.out.println("-----------------commands-----------------");
        System.out.println("help-------------------brings up this menu");
        System.out.println("list--------------shows all active players");
        System.out.println("queue-------------queues up to play a game");
        System.out.println("hint-------gives a valid move you can play");
        System.out.println("quit---------------------closes the client");
    }

    /**
     * Creates an instance of GameClientTUI and runs the TUI.
     *
     * @param args command line arguments (not used)
     * @throws InterruptedException if the thread is interrupted while sleeping
     */
    public static void main(String[] args) throws InterruptedException {
        ComputerTUI computerTUI = new ComputerTUI();
        computerTUI.runTUI();
    }

    /**
     * Notifies the listener that a message has been received.
     *
     * @param message the message received
     */
    @Override
    public void message(String message) {
        System.out.println(message);
    }

    /**
     * Notifies the listener that the connection to the server has been lost.
     */
    @Override
    public void connectionLost() {
        System.exit(0);
    }
}
