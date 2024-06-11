package networking.server;

import java.io.IOException;
import java.net.Socket;
import java.util.*;

import networking.protocol.Protocol;
import networking.SocketServer;

/**
 * Class that represents a server for a Dots and Boxes game which follows the predefined Protocol.
 */
public class GameServer extends SocketServer {


    /**
     * The Set of ClientHandlers for Logged-In users.
     */
    private final Set<ClientHandler> clients;

    /**
     * The Queue of ClientHandlers waiting to participate in the game.
     */
    private final Queue<ClientHandler> clientsQueue;

    /**
     * Description of the server.
     */
    private final String description;


    /**
     * Constructs a new GameServer instance. This constructor initializes the server on the specified port
     * and sets a description for the server and initializes the Set to keep track of clients and a LinkedList
     * as a queue for clients who wait in the game.
     * Inheriting from a SocketServer, it calls the constructor of the superclass with the provided port number.
     *
     * @param port        port number on which the server will listen for incoming client connections.
     * @param description string description of the server.
     * @throws IOException If an I/O error occurs when opening the server socket.
     */
    public GameServer(int port, String description) throws IOException {
        super(port);
        clients = new HashSet<>();
        clientsQueue = new LinkedList<>();
        this.description = description;
        waitForNewGameQueue();
    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     */
    @Override
    protected void handleConnection(Socket socket) {
        // Create a new ServerConnection and ClientHandler
        try {
            ServerConnection serverConnection = new ServerConnection(socket);
            ClientHandler clientHandler = new ClientHandler(this, serverConnection);

            // Set references between ServerConnection and ClientHandler
            serverConnection.setClientHandler(clientHandler);

            // Start the connection and handler
            serverConnection.start();
            clientHandler.start();

        } catch (IOException e) {
            System.out.println("Error: I/O Exception in handling the connection.");
        }

    }


    /**
     * Returns the port on which this server is listening for connections.
     *
     * @return the port on which this server is listening for connections
     */
    @Override
    public int getPort() {
        return super.getPort();
    }

    /**
     * Adds a client to the list of connected clients.
     *
     * @param clientHandler the client handler to add
     */
    public void addClient(ClientHandler clientHandler) {
        synchronized (clients) {
            clients.add(clientHandler);
        }
        System.out.println("Client added: " + clientHandler.getUsername());
    }

    /**
     * Removes a client from the list of connected clients.
     *
     * @param clientHandler the client handler to remove
     */
    public void removeClient(ClientHandler clientHandler) {
        synchronized (clients) {
            clients.remove(clientHandler);
        }
        System.out.println("Client removed: " + clientHandler.getUsername());
    }

    /**
     * Adds a ClientHandler player to the waiting queue if they are not already in the queue.
     *
     * @param clientHandler client to add in the queue.
     */
    public void joinQueue(ClientHandler clientHandler) {
        synchronized (clientsQueue) {
            if (!clientsQueue.contains(clientHandler) && clients.contains(clientHandler)) {
                clientsQueue.add(clientHandler);
                System.out.println("\nClient: " + clientHandler.getUsername() + " has joined the queue.");
                clientsQueue.notifyAll();
            } else {
                clientHandler.sendCommand(Protocol.ERROR);
            }
        }
    }

    /**
     * Method that creates and starts the separate listener threat that waits until client joins queue,
     * then checks the size of the Queue - if there are 2 or more clients it starts the new game on a separate thread.
     */
    public void waitForNewGameQueue() {
        new Thread(() -> {
            while (true) {
                synchronized (clientsQueue) {
                    while (clientsQueue.size() < 2) {
                        try {
                            clientsQueue.wait();
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                            return;
                        }
                    }
                    ClientHandler player1 = clientsQueue.poll();
                    ClientHandler player2 = clientsQueue.poll();
                    assert player1 != null;
                    assert player2 != null;
                    player1.handleNewGame();
                    player2.handleNewGame();
                    sendNewGame(player1, player2);
                    System.out.println("\n" + Protocol.NEWGAME + Protocol.SEPARATOR + player1.getUsername() + Protocol.SEPARATOR + player2.getUsername() + " have started a game.");
                    GameImplServer game = new GameImplServer(player1, player2);
                    new Thread(game).start();
                }
            }
        }).start();
    }

    /**
     * Sends a New Game message to both clients that start a game.
     *
     * @param p1 - player 1.
     * @param p2 - player 2.
     */
    public void sendNewGame(ClientHandler p1, ClientHandler p2) {
        String message = Protocol.NEWGAME + Protocol.SEPARATOR + p1.getUsername() +
                Protocol.SEPARATOR + p2.getUsername();
        p1.sendCommand(message);
        p2.sendCommand(message);
    }


    /**
     * Checks whether the client is already in the Queue, returns true if the client is in
     * the queue, otherwise false.
     *
     * @param clientHandler client to check the queue with.
     * @return true if the client is in the queue, false otherwise.
     */
    public boolean isInQueue(ClientHandler clientHandler) {
        return this.clientsQueue.contains(clientHandler);
    }

    /**
     * Removes a ClientHandler player from the waiting queue.
     *
     * @param clientHandler client to remove from the queue.
     */
    public void leaveQueue(ClientHandler clientHandler) {
        synchronized (clientsQueue) {
            clientsQueue.remove(clientHandler);
            System.out.println("\nClient: " + clientHandler.getUsername() + " has left the queue.");

        }
    }


    /**
     * Accepts connections and starts a new thread for each connection.
     * This method will block until the server socket is closed, for example by invoking closeServerSocket.
     *
     * @throws IOException if an I/O error occurs when waiting for a connection
     */
    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }


    /**
     * Closes the server socket. This will cause the server to stop accepting new connections.
     * If called from a different thread than the one running acceptConnections, then that thread will return from
     * acceptConnections.
     */
    @Override
    public synchronized void close() {
        super.close();
    }


    /**
     * Reply Hello~ServerDescription to the initial client's Hello handshake.
     *
     * @param clientHandler - clientHandler to reply with Hello.
     */
    public void handleHelloToClient(ClientHandler clientHandler) {
        clientHandler.sendHello(this.description);
    }

    /**
     * Implementation of Login command which tries to Save the clientHandler in the server
     * and reply's with LOGIN if successful, otherwise ALREADYLOGGEDIN if the client
     * with this name exists.
     *
     * @param clientHandler - clientHandler to add and reply to.
     */
    public void handleLogin(ClientHandler clientHandler, String username) {
        synchronized (clients) {
            if (checkUsername(username) && !isLoggedIn(clientHandler) && clientHandler.isHelloProtocol()) {
                clientHandler.setUsername(username);
                addClient(clientHandler);
                clientHandler.sendLogin(true);
            } else {
                clientHandler.sendLogin(false);
            }
        }
    }


    /**
     * Implementation of List command which sends the list of all logged in clients.
     *
     * @param clientHandler - clientHandler to add and reply to.
     */
    public void handleList(ClientHandler clientHandler) {
        if (isLoggedIn(clientHandler)) {
            StringBuilder message = new StringBuilder(Protocol.LIST);
            for (ClientHandler client : clients) {
                message.append(Protocol.SEPARATOR).append(client.getUsername());
            }
            clientHandler.sendCommand(message.toString());
        } else {
            clientHandler.sendCommand(Protocol.ERROR);
        }
    }


    /**
     * Check whether the client is Logged in. Returns true if the client is Logged in, otherwise - false.
     *
     * @param clientHandler clientHandler instance to check
     * @return true if logged in, false otherwise.
     */
    public boolean isLoggedIn(ClientHandler clientHandler) {
        return this.clients.contains(clientHandler);
    }

    /**
     * Check whether the user with this username exist, returns true if the username is not taken, otherwise false.
     *
     * @param user username to check
     * @return true if the username is not taken.
     */
    public boolean checkUsername(String user) {
        synchronized (clients) {
            for (ClientHandler client : clients) {
                if (client.getUsername().equals(user)) return false;
            }
            return true;
        }
    }


    /**
     * Main which handles the start of the server on the specific port based on the input from the Scanner.
     *
     * @param args string args
     */
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        System.out.print("\nEnter the Server Description: ");
        String desc = scanner.nextLine();
        GameServer server = null;
        while (server == null) {
            System.out.print("Enter the port number (or 0 for a random port): ");
            int port = getPort(scanner);
            scanner.nextLine();
            try {
                server = new GameServer(port, desc);
                System.out.println("Server started on port: " + server.getPort());
                server.acceptConnections();
            } catch (IOException e) {
                System.out.println("Error: I/O Exception in starting server.");
                System.out.println("\nTry using a different Port.\n");
                server = null;
            }
        }
    }

    /**
     * Used in the main to ask user about the port number using the scanner from main.
     *
     * @param scanner scanner of system in.e
     * @return the decided by the user port to use.
     */
    private static int getPort(Scanner scanner) {
        int port = -1;
        while (port < 0 || port > 65_535) {
            try {
                System.out.print("\nEnter a port number: ");
                port = scanner.nextInt();
            } catch (InputMismatchException e) {
                // Clear the buffer to prevent an infinite loop
                scanner.nextLine();
                System.out.println("Invalid port format. Please enter a valid number.");
            }
            if (port < 0 || port > 65_535) {
                System.out.println("Invalid port number the allowed ports are (0-65,535)");
            }
        }
        if (port == 0) {
            port = new Random().nextInt(65535);
        }
        return port;
    }

}
